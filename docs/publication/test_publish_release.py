import hashlib
import importlib.util
import io
from pathlib import Path
import unittest
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


if __name__ == '__main__':
    unittest.main()
