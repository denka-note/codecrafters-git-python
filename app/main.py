import hashlib
import os
import sys
import zlib
import http.client
import urllib.parse
from collections import deque
from io import BytesIO


def read_var_int(data, offset):
    value = 0
    shift = 0
    while True:
        byte = data[offset]
        offset += 1
        value |= (byte & 0x7F) << shift
        if not (byte & 0x80):
            break
        shift += 7
    return value, offset


def read_var_offset(data, offset):
    value = 0
    shift = 0
    while True:
        byte = data[offset]
        offset += 1
        value |= (byte & 0x7F) << shift
        if not (byte & 0x80):
            break
        value += 1
        shift += 7
    return value, offset


def store_object(content, obj_type):
    header = f"{obj_type} {len(content)}\0".encode()
    full_content = header + content
    hashed = hashlib.sha1(full_content).hexdigest()
    dir_path = os.path.join(".git", "objects", hashed[:2])
    file_path = os.path.join(dir_path, hashed[2:])
    os.makedirs(dir_path, exist_ok=True)
    with open(file_path, "wb") as f:
        f.write(zlib.compress(full_content))
    return hashed


def read_object(sha):
    file_path = os.path.join(".git", "objects", sha[:2], sha[2:])
    if not os.path.exists(file_path):
        return None, None, None
    with open(file_path, "rb") as f:
        compressed_data = f.read()
    data = zlib.decompress(compressed_data)
    header_end = data.find(b"\x00")
    header = data[:header_end].decode()
    obj_type, size_str = header.split()
    content = data[header_end + 1:]
    return obj_type, int(size_str), content


def git_init():
    os.makedirs(".git/objects", exist_ok=True)
    os.makedirs(".git/refs", exist_ok=True)
    with open(".git/HEAD", "w") as f:
        f.write("ref: refs/heads/main\n")


def checkout_tree(tree_sha, base_path="."):
    obj_type, _, tree_data = read_object(tree_sha)
    if obj_type != "tree":
        raise ValueError(f"Expected tree object, got {obj_type}")

    offset = 0
    while offset < len(tree_data):
        space_idx = tree_data.find(b' ', offset)
        null_idx = tree_data.find(b'\x00', space_idx)

        mode_str = tree_data[offset:space_idx].decode()
        name = tree_data[space_idx + 1:null_idx].decode("utf-8")
        entry_sha = tree_data[null_idx + 1: null_idx + 1 + 20].hex()
        offset = null_idx + 1 + 20

        full_path = os.path.join(base_path, name)

        if mode_str.startswith("4"):
            os.makedirs(full_path, exist_ok=True)
            checkout_tree(entry_sha, full_path)
        elif mode_str.startswith("10"):
            obj_type, _, blob_content = read_object(entry_sha)
            if obj_type != "blob":
                raise ValueError(f"Expected blob object, got {obj_type}")
            with open(full_path, "wb") as f:
                f.write(blob_content)
            if mode_str == "100755":
                os.chmod(full_path, os.stat(full_path).st_mode | 0o111)


def apply_delta(base_data, delta_data):
    delta_offset = 0

    base_size, delta_offset = read_var_int(delta_data, delta_offset)
    if base_size != len(base_data):
        raise ValueError("Base size mismatch in delta application")

    result_size, delta_offset = read_var_int(delta_data, delta_offset)
    result_data = bytearray()

    while delta_offset < len(delta_data):
        instruction = delta_data[delta_offset]
        delta_offset += 1

        if instruction & 0x80:
            offset_val = 0
            size_val = 0

            if instruction & 0x01:
                offset_val |= delta_data[delta_offset]
                delta_offset += 1
            if instruction & 0x02:
                offset_val |= delta_data[delta_offset] << 8
                delta_offset += 1
            if instruction & 0x04:
                offset_val |= delta_data[delta_offset] << 16
                delta_offset += 1
            if instruction & 0x08:
                offset_val |= delta_data[delta_offset] << 24
                delta_offset += 1

            if instruction & 0x10:
                size_val |= delta_data[delta_offset]
                delta_offset += 1
            if instruction & 0x20:
                size_val |= delta_data[delta_offset] << 8
                delta_offset += 1
            if instruction & 0x40:
                size_val |= delta_data[delta_offset] << 16
                delta_offset += 1

            if size_val == 0:
                size_val = 0x10000

            result_data.extend(base_data[offset_val: offset_val + size_val])
        else:
            add_size = instruction & 0x7F
            result_data.extend(delta_data[delta_offset: delta_offset + add_size])
            delta_offset += add_size

    if len(result_data) != result_size:
        raise ValueError(
            f"Result size mismatch after delta application: expected {result_size}, got {len(result_data)}")
    return bytes(result_data)


def parse_packfile(pack_data):
    if pack_data[0:4] != b"PACK":
        raise ValueError("Invalid packfile signature")
    version = int.from_bytes(pack_data[4:8], "big")
    num_objects = int.from_bytes(pack_data[8:12], "big")

    offset = 12

    resolved_objects = {}
    objects_by_offset = {}

    delta_queue = deque()

    for i in range(num_objects):
        object_start_offset = offset

        byte = pack_data[offset]
        offset += 1
        obj_type_code = (byte >> 4) & 0b111
        decompressed_size = byte & 0b1111
        shift = 4
        while byte & 0b10000000:
            byte = pack_data[offset]
            offset += 1
            decompressed_size |= (byte & 0b01111111) << shift
            shift += 7

        obj_type_map = {
            1: "commit", 2: "tree", 3: "blob", 4: "tag",
            6: "ofs_delta", 7: "ref_delta"
        }
        current_obj_type = obj_type_map.get(obj_type_code)

        base_ref = None
        if current_obj_type == "ofs_delta":
            base_offset_val, offset = read_var_offset(pack_data, offset)
            base_ref = object_start_offset - base_offset_val
        elif current_obj_type == "ref_delta":
            base_ref = pack_data[offset: offset + 20].hex()
            offset += 20

        compressed_data_start_offset = offset

        dco = zlib.decompressobj(wbits=zlib.MAX_WBITS)

        try:
            decompressed_obj_data = dco.decompress(pack_data[offset:])
            consumed_bytes_for_current_obj = len(pack_data[offset:]) - len(dco.unused_data)
            compressed_data_end_offset = offset + consumed_bytes_for_current_obj

            offset = compressed_data_end_offset

            if current_obj_type in ["ofs_delta", "ref_delta"]:
                delta_queue.append((object_start_offset, current_obj_type, base_ref,
                                    pack_data[compressed_data_start_offset:compressed_data_end_offset]))
            else:
                obj_sha = store_object(decompressed_obj_data, current_obj_type)
                resolved_objects[obj_sha] = (current_obj_type, decompressed_obj_data)
                objects_by_offset[object_start_offset] = (current_obj_type, decompressed_obj_data)

        except zlib.error as e:
            raise

    while delta_queue:
        start_offset, delta_type, base_ref, compressed_delta_data = delta_queue.popleft()

        base_obj_type = None
        base_obj_content = None

        if delta_type == "ofs_delta":
            if base_ref in objects_by_offset:
                base_obj_type, base_obj_content = objects_by_offset[base_ref]
            else:
                delta_queue.append((start_offset, delta_type, base_ref, compressed_delta_data))
                continue
        elif delta_type == "ref_delta":
            if base_ref in resolved_objects:
                base_obj_type, base_obj_content = resolved_objects[base_ref]
            else:
                delta_queue.append((start_offset, delta_type, base_ref, compressed_delta_data))
                continue

        if base_obj_content is None:
            raise RuntimeError(f"Could not find base object for delta at offset {start_offset}")

        dco = zlib.decompressobj(wbits=zlib.MAX_WBITS)
        delta_instructions = dco.decompress(compressed_delta_data)

        new_obj_content = apply_delta(base_obj_content, delta_instructions)
        new_obj_type = base_obj_type

        obj_sha = store_object(new_obj_content, new_obj_type)
        resolved_objects[obj_sha] = (new_obj_type, new_obj_content)
        objects_by_offset[start_offset] = (new_obj_type, new_obj_content)

    return list(resolved_objects.keys())


def ls_tree(hashed):
    obj_type, _, data = read_object(hashed)
    if obj_type != "tree":
        raise ValueError(f"Expected tree object, got {obj_type}")

    tree_data = data

    offset = 0
    while offset < len(tree_data):
        space_idx = tree_data.find(b' ', offset)
        null_idx = tree_data.find(b'\x00', space_idx)

        name = tree_data[space_idx + 1:null_idx].decode("utf-8")

        print(name)

        offset = null_idx + 1 + 20


def write_tree(target):
    entries = []
    for entry in sorted(os.listdir(target)):
        full_path = os.path.join(target, entry)
        if entry == ".git":
            continue

        if os.path.isdir(full_path):
            sha1 = write_tree(full_path)
            mode = "40000"
        else:
            with open(full_path, "rb") as f:
                content = f.read()
            sha1 = store_object(content, "blob")
            mode = "100644"
        entries.append(f"{mode} {entry}\0".encode() + bytes.fromhex(sha1))

    tree_data = b"".join(entries)
    tree_sha1 = store_object(tree_data, "tree")
    return tree_sha1


def commit_tree(tree_sha, parent_sha, message):
    parent_line = f"parent {parent_sha}\n" if parent_sha else ""
    content = f"tree {tree_sha}\n{parent_line}author Anunay <anunay@gmail.com>\ncommitter Anunay <anunay@gmail.com>\n\n{message}\n".encode()
    return store_object(content, "commit")


def main():
    command = sys.argv[1]
    if command == "init":
        git_init()

    elif command == "cat-file" and sys.argv[2] == "-p":
        file_sha = sys.argv[3]
        obj_type, _, content = read_object(file_sha)
        if content:
            print(content.decode("utf-8"), end="")
        else:
            raise RuntimeError(f"Object {file_sha} not found")

    elif command == "hash-object":
        if not sys.argv[2] == "-w":
            raise RuntimeError(f"Unexpected flag #{sys.argv[2]}")

        with open(sys.argv[3], "rb") as f:
            contents = f.read()

        hashed = store_object(contents, "blob")
        print(hashed)

    elif command == "ls-tree":
        if sys.argv[2] != "--name-only":
            raise RuntimeError(f"Unknown flag {sys.argv[2]}")
        ls_tree(sys.argv[3])

    elif command == "write-tree":
        print(write_tree("."))

    elif command == "commit-tree":
        tree_sha = sys.argv[2]
        parent_sha = sys.argv[4] if len(sys.argv) > 4 else None
        message = sys.argv[6]
        print(commit_tree(tree_sha, parent_sha, message))

    elif command == "clone":
        remote_url = sys.argv[2]
        target_dir = sys.argv[3]

        os.makedirs(target_dir, exist_ok=True)
        original_cwd = os.getcwd()
        os.chdir(target_dir)

        try:
            git_init()

            parsed_url = urllib.parse.urlparse(remote_url)
            host = parsed_url.netloc
            path_prefix = parsed_url.path
            if path_prefix.endswith(".git"):
                path_prefix = path_prefix[:-4]

            conn = None
            if parsed_url.scheme == "https":
                conn = http.client.HTTPSConnection(host)
            else:
                conn = http.client.HTTPConnection(host)

            info_refs_path = f"{path_prefix}.git/info/refs?service=git-upload-pack"
            conn.request("GET", info_refs_path)
            response = conn.getresponse()

            if response.status != 200:
                raise RuntimeError(f"Failed to fetch info/refs: {response.status} {response.reason}")

            refs = {}
            pkt_stream = BytesIO(response.read())

            while True:
                len_hex = pkt_stream.read(4)
                if not len_hex:
                    break
                line_len = int(len_hex, 16)
                if line_len == 0:
                    continue

                data = pkt_stream.read(line_len - 4)

                if b' ' in data and not data.startswith(b'#'):
                    sha_str, ref_name_str = data.split(b' ', 1)
                    refs[ref_name_str.decode().strip()] = sha_str.decode()

            conn.close()

            default_branch_sha = None
            if "refs/heads/main" in refs:
                default_branch_sha = refs["refs/heads/main"]
            elif "refs/heads/master" in refs:
                default_branch_sha = refs["refs/heads/master"]
            else:
                if "HEAD" in refs and refs["HEAD"].startswith("ref: "):
                    symbolic_ref = refs["HEAD"].split("ref: ")[1]
                    if symbolic_ref in refs:
                        default_branch_sha = refs[symbolic_ref]

            if not default_branch_sha:
                raise RuntimeError("Could not determine default branch SHA to clone.")

            conn = None
            if parsed_url.scheme == "https":
                conn = http.client.HTTPSConnection(host)
            else:
                conn = http.client.HTTPConnection(host)

            upload_pack_path = f"{path_prefix}.git/git-upload-pack"

            request_body = b''
            request_body += f"0032want {default_branch_sha}\n".encode()
            request_body += b"0000"
            request_body += b"0009done\n"

            headers = {
                "Content-Type": "application/x-git-upload-pack-request",
                "Accept": "application/x-git-upload-pack-result"
            }

            conn.request("POST", upload_pack_path, body=request_body, headers=headers)
            response = conn.getresponse()

            if response.status != 200:
                raise RuntimeError(f"Failed to fetch packfile: {response.status} {response.reason}")

            full_response_content = response.read()

            pack_signature_index = full_response_content.find(b"PACK")
            if pack_signature_index == -1:
                raise RuntimeError("Packfile signature 'PACK' not found in response.")

            pack_data = full_response_content[pack_signature_index:]

            conn.close()

            parse_packfile(pack_data)

            os.makedirs(os.path.join(".git", "refs", "heads"), exist_ok=True)
            with open(os.path.join(".git", "refs", "heads", "main"), "w") as f:
                f.write(default_branch_sha + "\n")

            with open(os.path.join(".git", "HEAD"), "w") as f:
                f.write("ref: refs/heads/main\n")

            commit_type, _, commit_content = read_object(default_branch_sha)
            if commit_type != "commit":
                raise ValueError(f"Expected commit object, got {commit_type}")

            tree_line = [line for line in commit_content.split(b'\n') if line.startswith(b'tree ')][0]
            tree_sha = tree_line.split(b' ')[1].decode()

            checkout_tree(tree_sha, ".")

        finally:
            os.chdir(original_cwd)

    else:
        raise RuntimeError(f"Unknown command #{command}")


if __name__ == "__main__":
    main()