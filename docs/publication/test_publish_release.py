import hashlib
import importlib.util
import io
import json
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch
import zipfile


class PublicationTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        spec = importlib.util.spec_from_file_location('publish_release', Path(__file__).with_name('publish_release.py'))
        cls.release = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(cls.release)

    def test_audited_proof_changes_are_rejected(self):
        old = {'README.md': 'a', 'NSP14/Main.lean': 'b'}
        self.release.check_baseline(old, {'README.md': 'c', 'NSP14/Main.lean': 'b', 'CITATION.cff': 'd'})
        with self.assertRaises(ValueError):
            self.release.check_baseline(old, {'README.md': 'c', 'NSP14/Main.lean': 'e'})
        with self.assertRaises(ValueError):
            self.release.check_baseline(old, {'README.md': 'c'})

    def test_asset_digest_must_match(self):
        self.release.check_digest(b'proof', hashlib.sha256(b'proof').hexdigest())
        with self.assertRaises(ValueError):
            self.release.check_digest(b'wrong', hashlib.sha256(b'proof').hexdigest())

    def record(self):
        return {'doi': '10.5281/zenodo.123', 'metadata': {
            'version': 'v1.0.0', 'creators': [{'orcid': '0009-0005-4230-0268'}],
            'related_identifiers': [{'identifier': 'https://github.com/stksk310/NS-P14-Lean/tree/v1.0.0'}]},
            'files': [{'key': 'source.zip', 'links': {'self': 'https://zenodo.org/api/records/123/files/source.zip/content'}}]}

    def test_record_binds_repository_version_author_and_doi(self):
        self.assertTrue(self.release.is_our_record(self.record()))
        for field, bad in [('version', 'v0.1.0'), ('creators', [{'orcid': '0000-0000-0000-0000'}]),
                           ('related_identifiers', [{'identifier': 'https://github.com/other/repo/tree/v1.0.0'}])]:
            record = self.record(); record['metadata'][field] = bad
            self.assertFalse(self.release.is_our_record(record))
        record = self.record(); record['doi'] = ''
        self.assertFalse(self.release.is_our_record(record))

    def archive(self, entries):
        stream = io.BytesIO()
        with zipfile.ZipFile(stream, 'w') as archive:
            for name, data in entries:
                archive.writestr(name, data)
        return stream.getvalue()

    def test_zenodo_archive_matches_all_tagged_bytes(self):
        expected = {'NSP14/Main.lean': self.release.blob_oid(b'proof'), '.zenodo.json': self.release.blob_oid(b'metadata')}
        self.release.verify_zip(self.archive([('repo/NSP14/Main.lean', b'proof'), ('repo/.zenodo.json', b'metadata')]), expected)
        for entries in [[('repo/NSP14/Main.lean', b'changed'), ('repo/.zenodo.json', b'metadata')],
                        [('repo/NSP14/Main.lean', b'proof')],
                        [('repo/../NSP14/Main.lean', b'proof'), ('repo/.zenodo.json', b'metadata')]]:
            with self.assertRaises(ValueError):
                self.release.verify_zip(self.archive(entries), expected)

    def test_published_assets_may_only_be_reused_identically(self):
        self.assertEqual(self.release.asset_action(False, True), 'upload')
        self.assertEqual(self.release.asset_action(True, True), 'reuse')
        with self.assertRaises(ValueError):
            self.release.asset_action(True, False)

    def exercise_publish(self, interrupted_draft):
        state = {'exists': interrupted_draft, 'draft': True, 'commands': []}
        def api(args, **kwargs):
            endpoint = args[2]
            release = {'tag_name': 'v1.0.0', 'draft': state['draft'], 'assets': [], 'html_url': 'https://github.com/stksk310/NS-P14-Lean/releases/tag/v1.0.0'}
            if endpoint.endswith('/releases'):
                return subprocess.CompletedProcess(args, 0, json.dumps([[release] if state['exists'] else []]), '')
            if '/releases/tags/' in endpoint and (not state['exists'] or state['draft']):
                return subprocess.CompletedProcess(args, 1, '', 'HTTP 404')
            return subprocess.CompletedProcess(args, 0, json.dumps(release), '')
        def command(*args):
            if args[0] == 'git': return 'fixed-commit'
            state['commands'].append(args)
            if args[2] == 'create': state['exists'] = True
            if args[2] == 'edit': state['draft'] = False
            return ''
        with patch.object(self.release.subprocess, 'run', side_effect=api), patch.object(self.release, 'run', side_effect=command):
            result = self.release.publish({'assets': {'LICENSE': 'unused-for-new-upload'}})
        self.assertFalse(result['draft'])
        self.assertEqual(sum(c[2] == 'create' for c in state['commands']), 0 if interrupted_draft else 1)
        self.assertEqual([c[2] for c in state['commands']][-2:], ['upload', 'edit'])

    def test_first_publish_can_find_the_new_draft(self):
        self.exercise_publish(False)

    def test_interrupted_draft_is_reused_without_duplicate_release(self):
        self.exercise_publish(True)

    def test_existing_doi_receipt_must_match_bytes(self):
        self.assertTrue(hasattr(self.release, 'upload_receipt'))
        with tempfile.TemporaryDirectory() as dest:
            path = Path(dest) / 'ZENODO_RECEIPT_v1.0.0.json'; path.write_bytes(b'correct receipt')
            state = {'assets': [{'name': path.name}]}
            for data in (b'correct receipt', b'wrong receipt'):
                def command(*args):
                    if args[2] == 'download':
                        (Path(args[args.index('--dir') + 1]) / path.name).write_bytes(data)
                    return ''
                with patch.object(self.release, 'release_state', return_value=state), patch.object(self.release, 'run', side_effect=command):
                    if data.startswith(b'wrong'):
                        with self.assertRaises(ValueError): self.release.upload_receipt(path)
                    else:
                        self.release.upload_receipt(path)


if __name__ == '__main__':
    unittest.main()
