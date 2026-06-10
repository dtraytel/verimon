#!/usr/bin/env python3
"""Minimal I/Q MCP client: authenticate (per-connection) then issue one tool call.

Usage:
  iqcall.py raw '<json-rpc request>'         # send one raw request (after auth)
  iqcall.py call <tool> '<json-args>'        # tools/call <tool> with json arguments
  iqcall.py list                             # tools/list (no auth needed but we auth anyway)

Env: IQ_TOKEN (auth token), IQ_PORT (default 8765), IQ_HOST (default 127.0.0.1)
"""
import sys, os, json, socket, time, itertools

HOST = os.environ.get("IQ_HOST", "127.0.0.1")
PORT = int(os.environ.get("IQ_PORT", "8765"))
TOKEN = os.environ.get("IQ_TOKEN", "") or "7a2a1c28-4a5a-43e8-a007-9173d1f212da"
TIMEOUT = float(os.environ.get("IQ_TIMEOUT", "300"))
THY = "/Users/kfx532/repos/verimon/thys/MFODL_Monitor_Devel/Monitor.thy"

_ids = itertools.count(1)

class Conn:
    def __init__(self):
        self.s = socket.create_connection((HOST, PORT), timeout=TIMEOUT)
        self.s.settimeout(TIMEOUT)
        self.buf = b""
    def send(self, obj):
        self.s.sendall((json.dumps(obj) + "\n").encode())
    def recv_id(self, rid):
        deadline = time.time() + TIMEOUT
        while True:
            while b"\n" in self.buf:
                line, self.buf = self.buf.split(b"\n", 1)
                line = line.strip()
                if not line:
                    continue
                msg = json.loads(line.decode("utf-8"))
                if msg.get("id") == rid:
                    return msg
            if time.time() >= deadline:
                raise TimeoutError("no response for id %r" % rid)
            chunk = self.s.recv(65536)
            if not chunk:
                raise ConnectionError("server closed connection")
            self.buf += chunk
    def request(self, method, params=None):
        rid = next(_ids)
        req = {"jsonrpc": "2.0", "id": rid, "method": method}
        if params is not None:
            req["params"] = params
        self.send(req)
        return self.recv_id(rid)

def main():
    if len(sys.argv) < 2:
        print("usage: iqcall.py [list|call <tool> <jsonargs>|raw <jsonreq>]", file=sys.stderr)
        sys.exit(2)
    mode = sys.argv[1]
    c = Conn()
    # initialize (always available)
    c.request("initialize", {"protocolVersion": "2024-11-05",
                             "capabilities": {},
                             "clientInfo": {"name": "iqcall", "version": "1.0"}})
    # authenticate (persists for the connection)
    auth = c.request("tools/call", {"name": "authenticate", "arguments": {"token": TOKEN}})
    # (we don't hard-fail on auth shape; print if error)
    if isinstance(auth, dict) and auth.get("error"):
        print(json.dumps(auth), flush=True)
        sys.exit(1)

    if mode == "list":
        print(json.dumps(c.request("tools/list"), indent=2))
    elif mode == "call":
        tool = sys.argv[2]
        args = json.loads(sys.argv[3]) if len(sys.argv) > 3 else {}
        print(json.dumps(c.request("tools/call", {"name": tool, "arguments": args}), indent=2))
    elif mode == "callf":
        tool = sys.argv[2]
        args = json.load(open(sys.argv[3]))
        print(json.dumps(c.request("tools/call", {"name": tool, "arguments": args}), indent=2))
    elif mode == "raw":
        req = json.loads(sys.argv[2])
        print(json.dumps(c.request(req["method"], req.get("params"))), flush=True)
    elif mode == "readlines":
        # readlines <start> <end> [path]
        start = int(sys.argv[2]); end = int(sys.argv[3])
        path = sys.argv[4] if len(sys.argv) > 4 else THY
        r = c.request("tools/call", {"name": "read_file",
              "arguments": {"path": path, "mode": "Line", "start_line": start, "end_line": end}})
        o = json.loads(r["result"]["content"][0]["text"])
        print(o["content"])
    elif mode == "readsearch":
        # readsearch <ctx> <pattern...>  (pattern may contain spaces; ctx is an int)
        ctx = int(sys.argv[2]); pat = " ".join(sys.argv[3:])
        r = c.request("tools/call", {"name": "read_file",
              "arguments": {"path": THY, "mode": "Search", "pattern": pat, "context_lines": ctx}})
        o = json.loads(r["result"]["content"][0]["text"])
        print(json.dumps(o, indent=1)[:6000])
    elif mode == "save":
        path = sys.argv[2] if len(sys.argv) > 2 else THY
        r = c.request("tools/call", {"name": "save_file", "arguments": {"path": path}})
        print(r["result"]["content"][0]["text"][:2000])
    elif mode == "reopen":
        path = sys.argv[2] if len(sys.argv) > 2 else THY
        r = c.request("tools/call", {"name": "open_file",
              "arguments": {"path": path, "view": True}})
        print(r["result"]["content"][0]["text"][:2000])
    elif mode == "sorries":
        path = sys.argv[2] if len(sys.argv) > 2 else THY
        r = c.request("tools/call", {"name": "get_sorry_positions", "arguments": {"path": path}})
        print(r["result"]["content"][0]["text"][:6000])
    elif mode == "status":
        path = sys.argv[2] if len(sys.argv) > 2 else THY
        import time as _t
        last = None
        _t.sleep(4)  # let PIDE register the buffer change before polling
        stable = 0
        for _ in range(28):  # ~60s cap: detect hangs/loops fast
            r = c.request("tools/call", {"name": "get_processing_status",
                                         "arguments": {"path": path}})
            o = json.loads(r["result"]["content"][0]["text"])
            last = o
            if o.get("fully_processed") and o.get("running", 0) == 0 and o.get("unprocessed", 0) == 0:
                stable += 1
                if stable >= 3:  # require 3 consecutive settled readings (~6s)
                    break
            else:
                stable = 0
            _t.sleep(2)
        print("status:", {k: last.get(k) for k in
              ("fully_processed", "unprocessed", "running", "error_count", "has_errors")})
        if last and last.get("error_count", 0) > 0:
            dr = c.request("tools/call", {"name": "get_diagnostics",
                  "arguments": {"scope": "file", "severity": "error", "path": path}})
            print("---ERRORS---")
            print(dr["result"]["content"][0]["text"][:6000])
    else:
        print("unknown mode", file=sys.stderr); sys.exit(2)

if __name__ == "__main__":
    main()
