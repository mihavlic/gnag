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

dot = '--dot' in args
watch = '--watch' in args
release = '--release' in args

if watch:
    args.remove('--watch')

if release:
    args.remove('--release')

if "--repeats" in args:
    print("--repeats is used, suppressing errors", file=sys.stderr)
    args += ['--errors', 'off']

files = [x for x in args if not x.startswith('--')]

observer = Observer()
observer.schedule(EventHandler(files), '.', recursive=True)

if watch:
    observer.start()

# Keep the script running
try:
    while True:
        if should_run:
            should_run = False
            command = ["cargo", "run", "--quiet", "--bin", "dump"]
            
            if release:
                command += ['--release']

            process = subprocess.run(command + ["--"] + args, capture_output=dot)
            
            if dot:
                sys.stderr.buffer.write(process.stderr)
                sys.stderr.flush()
                dotp = subprocess.run(["dot", "-T", "pdf", "-o", "target/dot.pdf"], input=process.stdout)

        if not watch:
            break
        
        time.sleep(0.1)
except KeyboardInterrupt:
    pass

if watch:
    observer.stop()
    observer.join()

