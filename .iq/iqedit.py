#!/usr/bin/env python3
"""Edit helper for I/Q write_file, reading literal text from files (no JSON escaping).

Usage:
  iqedit.py strreplace <thy_path> <old_txt_file> <new_txt_file>
  iqedit.py insert      <thy_path> <after_line:int> <new_txt_file>
  iqedit.py linereplace <thy_path> <start_line:int> <end_line:int> <new_txt_file>

Reuses iqcall.Conn for the authenticated connection.
"""
import sys, os, json
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import iqcall

def run(args):
    c = iqcall.Conn()
    c.request("initialize", {"protocolVersion": "2024-11-05", "capabilities": {},
                             "clientInfo": {"name": "iqedit", "version": "1.0"}})
    auth = c.request("tools/call", {"name": "authenticate",
                                    "arguments": {"token": iqcall.TOKEN}})
    if isinstance(auth, dict) and auth.get("error"):
        print(json.dumps(auth)); sys.exit(1)
    return c.request("tools/call", {"name": "write_file", "arguments": args})

def main():
    mode = sys.argv[1]
    path = sys.argv[2]
    if mode == "strreplace":
        old = open(sys.argv[3]).read()
        new = open(sys.argv[4]).read()
        args = {"path": path, "command": "str_replace", "old_str": old, "new_str": new}
    elif mode == "insert":
        after = int(sys.argv[3])
        new = open(sys.argv[4]).read()
        args = {"path": path, "command": "insert", "insert_line": after, "new_str": new}
    elif mode == "linereplace":
        start = int(sys.argv[3]); end = int(sys.argv[4])
        new = open(sys.argv[5]).read()
        args = {"path": path, "command": "line", "start_line": start, "end_line": end, "new_str": new}
    else:
        print("unknown mode", file=sys.stderr); sys.exit(2)
    print(json.dumps(run(args), indent=2))

if __name__ == "__main__":
    main()
