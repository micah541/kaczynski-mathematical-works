#!/usr/bin/env python3
"""Keep a Lean REPL alive so that checking a file costs seconds, not minutes.

Loading this project's imports (Mathlib + the differential-geometry library)
takes about 3 minutes. The REPL loads them once; later commands reuse the loaded
environment.

    python scripts/leanrepl.py serve                 # start (blocks; run in background)
    python scripts/leanrepl.py import ShortTime.Setting.Equation   # -> prints env id
    python scripts/leanrepl.py check FILE [--env N]  # elaborate FILE (imports stripped) in env N
    python scripts/leanrepl.py cmd 'example : 1 + 1 = 2 := rfl' [--env N]
    python scripts/leanrepl.py stop

The REPL binary is taken from $LEAN_REPL, defaulting to ../tools/repl (built from
leanprover-community/repl, tag v4.33.0, with toolchain v4.33.1).
"""
from __future__ import annotations

import json
import os
import subprocess
import sys
import threading
import urllib.request
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
PORT = int(os.environ.get("LEAN_REPL_PORT", "8765"))
REPL = Path(os.environ.get(
    "LEAN_REPL", ROOT.parent / "tools" / "repl" / ".lake" / "build" / "bin" / "repl.exe"))


class Repl:
    def __init__(self) -> None:
        env = dict(os.environ, LEAN_NUM_THREADS=os.environ.get("LEAN_NUM_THREADS", "4"))
        self.proc = subprocess.Popen(
            ["lake", "env", str(REPL)], cwd=ROOT, env=env,
            stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=sys.stderr,
            text=True, encoding="utf-8", bufsize=1)
        self.lock = threading.Lock()

    def send(self, obj: dict) -> dict:
        with self.lock:
            assert self.proc.stdin and self.proc.stdout
            self.proc.stdin.write(json.dumps(obj) + "\n\n")
            self.proc.stdin.flush()
            buf = ""
            while True:
                line = self.proc.stdout.readline()
                if line == "":
                    return {"error": "REPL process exited"}
                if line.strip() == "" and buf.strip():
                    try:
                        return json.loads(buf)
                    except json.JSONDecodeError:
                        pass
                buf += line


def serve() -> None:
    repl = Repl()

    class Handler(BaseHTTPRequestHandler):
        def do_POST(self):  # noqa: N802
            body = json.loads(self.rfile.read(int(self.headers["Content-Length"])))
            if body.get("stop"):
                self._reply({"stopped": True})
                repl.proc.kill()
                threading.Thread(target=server.shutdown).start()
                return
            self._reply(repl.send(body))

        def _reply(self, obj: dict) -> None:
            data = json.dumps(obj).encode()
            self.send_response(200)
            self.send_header("Content-Type", "application/json")
            self.send_header("Content-Length", str(len(data)))
            self.end_headers()
            self.wfile.write(data)

        def log_message(self, *args):  # silence
            pass

    server = ThreadingHTTPServer(("127.0.0.1", PORT), Handler)
    print(f"lean repl server on 127.0.0.1:{PORT}", flush=True)
    server.serve_forever()


def request(obj: dict) -> dict:
    req = urllib.request.Request(f"http://127.0.0.1:{PORT}", data=json.dumps(obj).encode(),
                                 headers={"Content-Type": "application/json"})
    with urllib.request.urlopen(req, timeout=3600) as r:
        return json.loads(r.read())


def report(res: dict) -> int:
    msgs = res.get("messages", [])
    errors = 0
    for m in msgs:
        pos = m.get("pos", {})
        sev = m.get("severity", "info")
        errors += sev == "error"
        print(f"{sev} {pos.get('line')}:{pos.get('column')}: {m.get('data', '').strip()}")
    for s in res.get("sorries", []):
        print(f"sorry at {s.get('pos', {}).get('line')}: {s.get('goal', '').strip()[-1500:]}")
    if "error" in res:
        print("ERROR:", res["error"])
        errors += 1
    print(f"env {res.get('env')}  ({errors} errors, {len(msgs)} messages)")
    return 1 if errors else 0


def main(argv: list[str]) -> int:
    if hasattr(sys.stdout, "reconfigure"):
        sys.stdout.reconfigure(encoding="utf-8")
    args = argv[1:]
    env = None
    if "--env" in args:
        i = args.index("--env")
        env = int(args[i + 1])
        del args[i:i + 2]
    if not args:
        print(__doc__)
        return 2
    cmd, rest = args[0], args[1:]
    if cmd == "serve":
        serve()
        return 0
    if cmd == "stop":
        print(request({"stop": True}))
        return 0
    if cmd == "import":
        res = request({"cmd": "\n".join(f"import {m}" for m in rest)})
        code = report(res)
        # A missing .olean can yield an empty environment without any error message.
        probe = request({"cmd": "#check Nat.succ_le_of_lt", "env": res.get("env")})
        if any(m.get("severity") == "error" for m in probe.get("messages", [])) or "error" in probe:
            print("ERROR: the imported environment is empty (are all modules built?)")
            return 1
        return code
    if cmd == "cmd":
        obj = {"cmd": rest[0]}
    elif cmd == "check":
        text = Path(rest[0]).read_text(encoding="utf-8")
        lines = text.splitlines()
        body = [ln for ln in lines if not ln.startswith("import ")]
        # keep line numbers aligned with the file
        obj = {"cmd": "\n".join("" if ln.startswith("import ") else ln for ln in lines)}
        _ = body
    else:
        print(__doc__)
        return 2
    if env is not None:
        obj["env"] = env
    return report(request(obj))


if __name__ == "__main__":
    sys.exit(main(sys.argv))
