#!/usr/bin/env python3
"""Validate/publish the fixed release, then verify Zenodo's tagged source bytes.

Default mode is read-only. Publishing requires --publish and a checkout of TAG.
This validates release provenance, not Lean mathematical correctness anew.
"""
import argparse
import hashlib
import io
import json
from pathlib import Path, PurePosixPath
import subprocess
import tempfile
import time
import urllib.error
import urllib.parse
import urllib.request
import zipfile

ROOT = Path(__file__).resolve().parents[2]
REPO = 'stksk310/NS-P14-Lean'
TAG = 'v1.0.0'
ORCID = '0009-0005-4230-0268'
MANIFEST = ROOT / 'docs/publication/RELEASE_MANIFEST_v1.0.0.json'
NOTES = ROOT / 'docs/publication/RELEASE_NOTES_v1.0.0.md'


def run(*args):
    return subprocess.check_output(args, cwd=ROOT, text=True).strip()


def git_tree(revision):
    raw = subprocess.check_output(['git', 'ls-tree', '-rz', revision], cwd=ROOT)
    return {entry.split(b'\t', 1)[1].decode(): entry.split(b'\t', 1)[0].split()[2].decode()
            for entry in raw.split(b'\0') if entry}


def check_baseline(baseline, current):
    for name, oid in baseline.items():
        if name != 'README.md' and current.get(name) != oid:
            raise ValueError('audited file changed or missing: ' + name)


def check_digest(data, expected):
    if hashlib.sha256(data).hexdigest() != expected:
        raise ValueError('SHA-256 mismatch')


def blob_oid(data):
    return hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()


def is_our_record(record):
    meta = record.get('metadata', {})
    identifiers = {r.get('identifier', '').rstrip('/') for r in meta.get('related_identifiers', [])}
    urls = {f'https://github.com/{REPO}/tree/{TAG}', f'https://github.com/{REPO}/releases/tag/{TAG}'}
    creators = {c.get('orcid', '').removeprefix('https://orcid.org/') for c in meta.get('creators', [])}
    doi = record.get('doi') or meta.get('doi', '')
    return bool(meta.get('version') in (TAG, TAG[1:]) and identifiers & urls
                and ORCID in creators and doi.startswith('10.5281/zenodo.'))


def verify_zip(data, expected):
    with zipfile.ZipFile(io.BytesIO(data)) as archive:
        found = {}; prefixes = set()
        for info in archive.infolist():
            path = PurePosixPath(info.filename)
            if path.is_absolute() or '..' in path.parts or '\\' in info.filename:
                raise ValueError('unsafe ZIP path')
            if info.is_dir():
                continue
            if len(path.parts) < 2:
                raise ValueError('source ZIP must have one repository prefix')
            prefixes.add(path.parts[0]); name = '/'.join(path.parts[1:])
            if name in found:
                raise ValueError('duplicate ZIP entry')
            found[name] = blob_oid(archive.read(info))
        if len(prefixes) != 1 or found != expected:
            raise ValueError('Zenodo source ZIP differs from tagged Git tree')
    return len(found)


def asset_action(exists, identical):
    if exists and not identical:
        raise ValueError('refusing to replace an existing release asset')
    return 'reuse' if exists else 'upload'


def validate():
    manifest = json.loads(MANIFEST.read_text())
    current = git_tree('HEAD')
    check_baseline(git_tree(manifest['audited_commit']), current)
    for name, digest in manifest['assets'].items():
        check_digest((ROOT / name).read_bytes(), digest)
    for name, digest in manifest['evidence'].items():
        check_digest((ROOT / name).read_bytes(), digest)
    receipt = json.loads((ROOT / manifest['completion_receipt']).read_text())
    if receipt.get('all_P14_complete') is not True:
        raise ValueError('missing completed P14 receipt')
    meta = json.loads((ROOT / '.zenodo.json').read_text())
    if meta.get('version') != TAG[1:] or meta.get('creators') != [{'name': 'Sato, Keisuke', 'orcid': ORCID}]:
        raise ValueError('release metadata differs')
    if run('git', 'status', '--porcelain'):
        raise ValueError('release checkout is not clean')
    print('PASS: audited tree, evidence, assets, metadata, clean checkout', flush=True)
    return manifest, current


def release_state():
    # The by-tag REST endpoint excludes drafts. Authenticated listing includes
    # them, so first publication and retries can retrieve their own draft.
    result = subprocess.run(['gh', 'api', f'repos/{REPO}/releases', '--paginate', '--slurp'], cwd=ROOT,
                            text=True, capture_output=True)
    if result.returncode != 0:
        raise RuntimeError('GitHub release lookup failed: ' + result.stderr)
    matches = [release for page in json.loads(result.stdout) for release in page if release['tag_name'] == TAG]
    if len(matches) > 1:
        raise ValueError('multiple releases with the same tag')
    return matches[0] if matches else None


def publish(manifest):
    if run('git', 'rev-parse', 'HEAD') != run('git', 'rev-parse', f'{TAG}^{{commit}}'):
        raise ValueError('HEAD is not the release tag')
    release = release_state()
    if release is None:
        run('gh', 'release', 'create', TAG, '--repo', REPO, '--verify-tag', '--draft',
            '--title', 'NS-P14-Lean v1.0.0 — audited P14 formalization', '--notes-file', str(NOTES))
        release = release_state()
    for name, digest in manifest['assets'].items():
        path = ROOT / name
        exists = any(a['name'] == path.name for a in release['assets'])
        identical = True
        if exists:
            with tempfile.TemporaryDirectory() as dest:
                run('gh', 'release', 'download', TAG, '--repo', REPO, '--pattern', path.name, '--dir', dest)
                identical = hashlib.sha256((Path(dest) / path.name).read_bytes()).hexdigest() == digest
        if asset_action(exists, identical) == 'upload':
            run('gh', 'release', 'upload', TAG, str(path), '--repo', REPO)
    if release['draft']:
        run('gh', 'release', 'edit', TAG, '--repo', REPO, '--draft=false', '--latest')
    result = release_state()
    if result is None or result['draft']:
        raise RuntimeError('GitHub release is not published')
    print('GITHUB_RELEASE=' + result['html_url'], flush=True)
    return result


def fetch_json(url):
    request = urllib.request.Request(url, headers={'User-Agent': 'NS-P14-Lean-release-verification/1.0'})
    with urllib.request.urlopen(request, timeout=60) as response:
        return json.load(response)


def upload_receipt(path):
    release = release_state()
    exists = any(a['name'] == path.name for a in release['assets'])
    identical = True
    if exists:
        with tempfile.TemporaryDirectory() as dest:
            run('gh', 'release', 'download', TAG, '--repo', REPO, '--pattern', path.name, '--dir', dest)
            identical = (Path(dest) / path.name).read_bytes() == path.read_bytes()
    if asset_action(exists, identical) == 'upload':
        run('gh', 'release', 'upload', TAG, str(path), '--repo', REPO)


def verify_zenodo(expected, timeout):
    query = urllib.parse.urlencode({'q': '"NS-P14-Lean"', 'size': 100, 'sort': 'mostrecent'})
    deadline = time.monotonic() + timeout
    while True:
        try:
            records = fetch_json('https://zenodo.org/api/records?' + query)['hits']['hits']
            matches = [r for r in records if is_our_record(r)]
            if len(matches) > 1:
                raise ValueError('multiple matching Zenodo records; refusing to guess')
            if matches:
                record = fetch_json(f"https://zenodo.org/api/records/{int(matches[0]['id'])}")
                if not is_our_record(record):
                    raise ValueError('Zenodo record identity changed')
                zips = [f for f in record.get('files', []) if f.get('key', '').endswith('.zip')]
                if len(zips) != 1:
                    raise ValueError('expected exactly one source ZIP in the GitHub integration record')
                file = zips[0]; url = file['links']['self']; parsed = urllib.parse.urlsplit(url)
                if parsed.scheme != 'https' or parsed.hostname != 'zenodo.org':
                    raise ValueError('unexpected archive download origin')
                with urllib.request.urlopen(url, timeout=180) as response:
                    data = response.read()
                count = verify_zip(data, expected)
                return {'record_id': record['id'], 'version_doi': record.get('doi') or record['metadata']['doi'],
                        'concept_doi': record.get('conceptdoi'), 'record_url': record['links']['html'],
                        'source_file': file['key'], 'source_zip_sha256': hashlib.sha256(data).hexdigest(),
                        'tagged_files_verified': count}
        except (urllib.error.URLError, TimeoutError) as error:
            print('Zenodo query/download pending: ' + str(error), flush=True)
        if time.monotonic() >= deadline:
            raise TimeoutError('GitHub release published, but Zenodo archival/DOI could not yet be verified')
        print('Waiting for the Zenodo GitHub integration/index...', flush=True)
        time.sleep(min(30, max(0, deadline - time.monotonic())))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--publish', action='store_true')
    parser.add_argument('--zenodo-timeout', type=int, default=1200)
    args = parser.parse_args()
    manifest, expected = validate()
    if not args.publish:
        return
    release = publish(manifest)
    receipt = verify_zenodo(expected, args.zenodo_timeout)
    receipt.update({'tag': TAG, 'tag_commit': run('git', 'rev-parse', 'HEAD'),
                    'audited_commit': manifest['audited_commit'], 'github_release': release['html_url'],
                    'scope': 'Saved audit provenance and exact Zenodo/tag archive byte comparison; no new Lean run.'})
    with tempfile.TemporaryDirectory() as dest:
        receipt_path = Path(dest) / 'ZENODO_RECEIPT_v1.0.0.json'
        receipt_path.write_text(json.dumps(receipt, indent=2) + '\n')
        upload_receipt(receipt_path)
        notes = Path(dest) / 'release-notes.md'
        notes.write_text(NOTES.read_text() + '\n\nZenodo version DOI: https://doi.org/' + receipt['version_doi'] + '\n')
        run('gh', 'release', 'edit', TAG, '--repo', REPO, '--notes-file', str(notes))
    print(json.dumps(receipt, indent=2), flush=True)


if __name__ == '__main__':
    main()
