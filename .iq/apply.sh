#!/bin/bash
# apply.sh <old.txt> <new.txt> : str_replace edit + processing status + error diagnostics
export IQ_TOKEN=7a2a1c28-4a5a-43e8-a007-9173d1f212da
THY=/Users/kfx532/repos/verimon/thys/MFODL_Monitor_Devel/Monitor.thy
cd /Users/kfx532/repos/verimon
RESP=$(timeout 240 python3 .iq/iqedit.py strreplace "$THY" "$1" "$2" 2>&1)
echo "$RESP" | python3 -c '
import json,sys
try:
  d=json.load(sys.stdin)
except: print("RAWWRITE:",sys.stdin.read()[:600]); sys.exit()
if "error" in d: print("WRITE ERROR:",d["error"]["message"]); sys.exit(1)
print("write: ok")
'
# poll status until fully processed (or timeout)
for i in $(seq 1 40); do
  ST=$(timeout 60 python3 .iq/iqcall.py call get_processing_status "{\"path\":\"$THY\"}" 2>/dev/null | python3 -c '
import json,sys; d=json.load(sys.stdin); o=json.loads(d["result"]["content"][0]["text"])
print(int(o["fully_processed"]), o["unprocessed"], o["running"], o["error_count"], o["has_errors"])
')
  set -- $ST
  echo "poll $i: fully=$1 unproc=$2 running=$3 errors=$4"
  if [ "$1" = "1" ]; then break; fi
  sleep 6
done
