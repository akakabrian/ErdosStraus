#!/usr/bin/env python3
"""Execution guards. These validate run setup, not Lean proofs."""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import sys

EXPECTED_LEAN = '4.27.0'
EXECUTION_SUPPORT = (
    'GoalCheck.lean', 'TARGET.sha256', 'lean-toolchain', 'lakefile.toml',
    'verify.sh', 'static_audit.py', 'check_axioms.py', 'verification_guards.py',
)

def validate_lean_version(text: str) -> str:
    """Require a single actual version banner and an exact release token."""
    match = re.fullmatch(r'Lean \(version ([^\s,)]+)(?:, [^()\r\n]*)?\)', text.strip())
    if match is None or match.group(1) != EXPECTED_LEAN:
        raise ValueError(f'Expected exactly Lean {EXPECTED_LEAN}, not {text.strip()!r}')
    return match.group(1)

def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()

def support_hashes(root: Path) -> dict[str,str]:
    return {name: sha256(root/name) for name in EXECUTION_SUPPORT}

def stage_sources(root: Path, destination: Path, audit: dict) -> None:
    """Copy only audited Lean source, never source-adjacent cached objects."""
    destination = destination.resolve()
    for relative, info in audit['files'].items():
        source = root/relative
        target = (destination/relative).resolve()
        if not target.is_relative_to(destination):
            raise ValueError(f'Unsafe source path in audit: {relative!r}')
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, target)
        if sha256(target) != info['sha256']:
            raise ValueError(f'Source changed while creating snapshot: {relative}')

def normalized_lean_path(value: str, workspace: Path, build_out: Path) -> str:
    """Lake paths may be relative to its workspace, not to the staged sources."""
    entries = [str(build_out.resolve())]
    if value:
        for entry in value.split(os.pathsep):
            path = Path(entry) if entry else Path('.')
            entries.append(str((path if path.is_absolute() else workspace/path).resolve()))
    return os.pathsep.join(dict.fromkeys(entries))

def main() -> int:
    parser=argparse.ArgumentParser(description=__doc__)
    commands=parser.add_subparsers(dest='command',required=True)
    version=commands.add_parser('version'); version.add_argument('banner',type=Path)
    snap=commands.add_parser('snapshot')
    snap.add_argument('root',type=Path); snap.add_argument('destination',type=Path)
    snap.add_argument('audit',type=Path); snap.add_argument('manifest',type=Path)
    unchanged=commands.add_parser('unchanged')
    unchanged.add_argument('root',type=Path); unchanged.add_argument('manifest',type=Path)
    runner=commands.add_parser('run-lean')
    runner.add_argument('stage',type=Path); runner.add_argument('build_out',type=Path)
    runner.add_argument('lean_args',nargs=argparse.REMAINDER)
    args=parser.parse_args()
    try:
        if args.command=='version':
            print('Exact Lean release accepted:',validate_lean_version(args.banner.read_text()))
        elif args.command=='snapshot':
            audit=json.loads(args.audit.read_text())
            before=support_hashes(args.root)
            stage_sources(args.root,args.destination,audit)
            if before != support_hashes(args.root):
                raise ValueError('Verification support files changed during snapshot creation')
            args.manifest.write_text(json.dumps(before,indent=2)+'\n')
        elif args.command=='unchanged':
            before=json.loads(args.manifest.read_text())
            if before != support_hashes(args.root):
                raise ValueError('Verification support files changed during execution')
        elif args.command=='run-lean':
            workspace=Path.cwd()
            os.environ['LEAN_PATH']=normalized_lean_path(
                os.environ.get('LEAN_PATH',''),workspace,args.build_out)
            arguments=args.lean_args
            if arguments and arguments[0]=='--': arguments=arguments[1:]
            os.chdir(args.stage)
            os.execvp('lean',['lean',*arguments])
    except (OSError,ValueError,KeyError) as exc:
        print(f'EXECUTION GUARD FAILED: {exc}',file=sys.stderr)
        return 1
    return 0

if __name__=='__main__': raise SystemExit(main())
