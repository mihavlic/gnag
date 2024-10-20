#!/bin/python

from watchdog.observers import Observer
from watchdog.events import FileSystemEventHandler
import time, sys, subprocess, io

should_run = True

class EventHandler(FileSystemEventHandler):
    def __init__(self, paths: list[str]):
        self.paths = paths

    def on_modified(self, event):
        global should_run

        for path in self.paths:
            if event.src_path.endswith(path):
                should_run = True
                return

args = sys.argv[1:]

watch = '--watch' in args
release = '--release' in args
generate = '--generate' in args
debug = '--debug' in args

if watch:
    args.remove('--watch')

if release:
    args.remove('--release')

if generate:
    args.remove('--generate')
    args += ['--file']
    
if debug:
    args.remove('--debug')
    
if "--repeats" in args:
    print("--repeats is used, suppressing errors", file=sys.stderr)
    args += ['--errors', 'off']

files = [x for x in args if not x.startswith('--')]

observer = Observer()
observer.schedule(EventHandler(files), '.', recursive=True)

def run():
    command = ["cargo", "build", "--quiet", "--bin", "gnag-cli"]

    path = "target/debug/gnag-cli"
    
    if release:
        command += ['--release']
        path = "target/release/gnag-cli"

    # build cli
    a = subprocess.run(command)
    
    # run binary
    if debug:
        subprocess.run(["rust-gdb", "--quiet", "--args", path] + args)
        os.exit(0)
    else:
        capture_output = generate
        process = subprocess.run([path] + args, capture_output=capture_output)
    
        if capture_output:
            sys.stderr.buffer.write(process.stderr)
            sys.stderr.flush()
            if generate:
                output_path = "crates/gnag-parser/src/lib.rs"
                with open(output_path, "wb") as output:
                    output.write(process.stdout)
                print(f"Generated file written to {output_path}", file=sys.stderr)

if watch:
    observer.start()

# Keep the script running
try:
    while True:
        if should_run:
            run()
            should_run = False
        if not watch:
            break
        
        time.sleep(0.1)
except KeyboardInterrupt:
    pass

if watch:
    observer.stop()
    observer.join()

