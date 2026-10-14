#!/usr/bin/env python3
"""Block local originals, non-English scripts, and unreviewable binaries in Git.

Latin-script language still needs human review; mathematical Greek is allowed.
This gate is not a language translator or a mathematical certificate.
"""
import argparse
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import unicodedata


def git(*args):
    return subprocess.check_output(['git', *args])


def check_text(text):
    text = re.sub(r'\\u([0-9a-fA-F]{4})', lambda m: chr(int(m[1], 16)), text)
    for char in text:
        category = unicodedata.category(char)
        name = ' '.join(unicodedata.name(c, '') for c in unicodedata.normalize('NFKD', char))
        if category == 'Cs' or (category.startswith('L') and not
                              (0x2100 <= ord(char) <= 0x214f or
                               any(word in name for word in ('LATIN', 'GREEK', 'MATHEMATICAL')))):
            raise ValueError('non-English script; prepare a reviewed English version')


def check_file(path, data, mode='100644'):
    check_text(path)
    if any(part in {'local', '.compatibility', '.lake', '__pycache__'} for part in Path(path).parts):
        raise ValueError('local-only material must not enter Git')
    if mode == '120000':
        raise ValueError('compatibility or external-source symlink must stay local')
    if Path(path).suffix.lower() == '.pdf':
        with tempfile.NamedTemporaryFile(suffix='.pdf') as f:
            f.write(data); f.flush()
            text = subprocess.check_output(['pdftotext', f.name, '-']).decode('utf-8')
        if not any(c.isalpha() for c in text):
            raise ValueError('PDF has no inspectable text; prepare a reviewed text version')
    else:
        if b'\x00' in data or data.startswith((b'PK\x03\x04', b'\x1f\x8b', b'%PDF')):
            raise ValueError('archive or binary requires a separate reviewed English export')
        text = data.decode('utf-8')
        if Path(path).suffix.lower() == '.json':
            text = json.dumps(json.loads(text), ensure_ascii=False)
    check_text(text)


def check_index(ref=None):
    command = ('ls-tree', '-rz', ref) if ref else ('ls-files', '--stage', '-z')
    failures = []
    for record in git(*command).split(b'\0'):
        if not record:
            continue
        metadata, name = record.split(b'\t', 1)
        fields = metadata.split()
        mode, blob = fields[0].decode(), fields[2 if ref else 1].decode()
        path = name.decode('utf-8')
        try:
            if not ref and fields[2] != b'0':
                raise ValueError('unmerged index')
            if mode == '160000':
                raise ValueError('submodule content needs its own English review')
            check_file(path, git('cat-file', 'blob', blob), mode)
        except (ValueError, UnicodeError, OSError, subprocess.CalledProcessError) as error:
            failures.append(f'{path}: {error}')
    if failures:
        raise ValueError('\n'.join(failures))


def check_candidates():
    paths = git('ls-files', '--cached', '--others', '--exclude-standard', '-z').split(b'\0')
    failures = []; count = 0
    for name in paths:
        if not name:
            continue
        path = Path(name.decode())
        try:
            check_file(str(path), path.read_bytes(), '120000' if path.is_symlink() else '100644')
            count += 1
        except (ValueError, UnicodeError, OSError, subprocess.CalledProcessError) as error:
            failures.append(f'{path}: {error}')
    if failures:
        raise ValueError('\n'.join(failures))
    print(f'PASS: {count} Git candidate files; Latin-script prose requires human English review.')


def check_outgoing():
    seen = set()
    for line in sys.stdin:
        _, local_sha, _, remote_sha = line.split()
        if local_sha == '0' * 40:
            continue
        args = ['rev-list', local_sha]
        if remote_sha != '0' * 40 and subprocess.run(
                ['git', 'cat-file', '-e', remote_sha], capture_output=True).returncode == 0:
            args += ['^' + remote_sha]
        for commit in git(*args).decode().splitlines():
            if commit not in seen:
                check_text(git('show', '-s', '--format=%B', commit).decode())
                check_index(commit)
                seen.add(commit)


def self_test():
    import os
    import zipfile
    check_text('English prose: zeta, \u03b6, \u03b8, \u0393, Teichm\u00fcller; \u211d, \u2115, \u2113, \u207f.')
    def rejects(call):
        try:
            call()
        except (ValueError, UnicodeError):
            return
        raise AssertionError('gate accepted forbidden content')
    foreign = chr(20013)
    rejects(lambda: check_text(foreign))
    rejects(lambda: check_text('\\u' + format(ord(foreign), '04x')))
    rejects(lambda: check_file('local/original.md', b'English'))
    rejects(lambda: check_file('reference', b'../local', '120000'))
    rejects(lambda: check_file('sample.json', json.dumps({'note': foreign}).encode()))
    with tempfile.TemporaryDirectory() as folder:
        old = Path.cwd()
        try:
            os.chdir(folder)
            subprocess.run(['git', 'init', '-q'], check=True)
            for key, value in [('user.name', 'English Test'), ('user.email', 'test@example.invalid')]:
                subprocess.run(['git', 'config', key, value], check=True)
            Path('test.md').write_text('English math: zeta.')
            subprocess.run(['git', 'add', 'test.md'], check=True)
            check_index()
            # Check staged bytes even if the working copy has already been repaired.
            Path('test.md').write_text(foreign)
            subprocess.run(['git', 'add', 'test.md'], check=True)
            Path('test.md').write_text('English')
            rejects(check_index)
            subprocess.run(['git', 'commit', '-qm', 'Preserve a forbidden fixture'], check=True)
            bad = git('rev-parse', 'HEAD').decode().strip()
            rejects(lambda: check_index(bad))
            subprocess.run(['git', 'rm', '-q', '-f', 'test.md'], check=True)
            subprocess.run(['git', 'commit', '-qm', 'Delete the fixture'], check=True)
            check_index('HEAD')
            import io
            original_stdin = sys.stdin
            try:
                sys.stdin = io.StringIO(f'refs/heads/main {git("rev-parse", "HEAD").decode().strip()} refs/heads/main {"0"*40}\n')
                rejects(check_outgoing)
            finally:
                sys.stdin = original_stdin
            with zipfile.ZipFile('archive.zip', 'w') as archive:
                archive.writestr('English-name.md', foreign)
            rejects(lambda: check_file('archive.zip', Path('archive.zip').read_bytes()))
        finally:
            os.chdir(old)
    print('PASS: English/math, filenames/content, escapes, JSON, staged blobs, symlinks, archives, and deleted-history checks.')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument('--index', action='store_true')
    group.add_argument('--tree')
    group.add_argument('--candidates', action='store_true')
    group.add_argument('--message', type=Path)
    group.add_argument('--push', action='store_true')
    group.add_argument('--self-test', action='store_true')
    args = parser.parse_args()
    if args.self_test:
        self_test(); return
    if args.message:
        check_text(args.message.read_text()); return
    os_root = git('rev-parse', '--show-toplevel').decode().strip()
    import os
    os.chdir(os_root)
    if args.candidates:
        check_candidates()
    elif args.push:
        check_outgoing()
    else:
        check_index(args.tree)


if __name__ == '__main__':
    try:
        main()
    except (ValueError, UnicodeError, OSError, subprocess.CalledProcessError) as error:
        print(f'English publication gate FAILED: {error}', file=sys.stderr)
        sys.exit(1)
