from pathlib import Path
import json,re,hashlib,subprocess
mods=json.load(open('verification/run19/sources/three_port_modules.json'))
header='''module
public import NSP14.SmallEmbedding.Base
public import NSP14.Endpoint.NativeTransfer
public import NSP14.Endpoint.SocleBounds
public import NSP14.Endpoint.CoreAugmentation
public import NSP14.Width.EdgeAP
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 4096
open scoped Classical BigOperators
open NSP14.Endpoint CategoryTheory CategoryTheory.Limits HomologicalComplex NSP14.Homological

/-! Positive-alphabet version of the existing actual endpoint construction.
The original Endpoint.Data API remains byte-for-byte unchanged. Its old lower bound
on alphabet cardinality is used only to prove nonemptiness in these common modules.
Every proof below is replayed for the positive-alphabet structure, with no new
Tor/resource/comparison premise. The one-letter specialization is consumed in LanTuVu.
Source correspondence and hashes: verification/run19/sources/three-positive-endpoint-port_20261116.json.
-/
'''
parts=[header]; receipts=[]
for n in mods:
 p=Path(n.replace('.','/')+'.lean');s=p.read_text()
 sha=hashlib.sha256(p.read_bytes()).hexdigest()
 receipts.append({'module':n,'path':str(p),'sha256':sha,'base_git_blob':subprocess.check_output(['git','rev-parse','04906ede0e9e3a04b9c07c791c1e1c49834dd3e1:'+str(p)],text=True).strip()})
 if n=='NSP14.Endpoint.Data':
  body=s[s.index('namespace NSP14.Endpoint'):]
  body=body.replace('namespace NSP14.Endpoint','namespace NSP14.SmallEmbedding').replace('end NSP14.Endpoint','end NSP14.SmallEmbedding')
 else:
  matches=re.findall(r'namespace NSP14\.Endpoint\.Data\n.*?end NSP14\.Endpoint\.Data',s,re.S)
  assert matches,n
  body='\n'.join(matches)
 body=body.replace('NSP14.Endpoint.Data','NSP14.SmallEmbedding.ThreeData')
 body=re.sub(r'(?<![.\w])Data\b','ThreeData',body)
 body=body.replace('q_two','q_one').replace('q_one : 2 ≤ a.card','q_one : 1 ≤ a.card')
 prefix=s[:s.index('namespace ')]
 commands='\n'.join(l for l in prefix.splitlines() if l.startswith(('open ','set_option ','attribute ')))
 parts.extend([f'\n-- Replayed common endpoint module: {n}; source SHA256 {sha}.\n',commands+'\n',body+'\n'])
assert Path('NSP14/SmallEmbedding/ThreePresentation.lean').read_text()==''.join(parts), 'positive-alphabet port differs'
receipt={'base':'04906ede0e9e3a04b9c07c791c1e1c49834dd3e1','sources':receipts,'adaptation':['New namespace NSP14.SmallEmbedding.ThreeData','Only structure lower bound q_one : 1 ≤ a.card (old q_two was used only for nonemptiness)','Replay all common actual endpoint proofs with the weaker positive-alphabet structure','Generic Endpoint/ArithmeticSequence library declarations are reused, not duplicated','Old Endpoint files and their public types remain unchanged'],'scope':'Foundations only; no claim that the two remaining Run19 contracts are closed.'}
print('PASS_EXACT_POSITIVE_ALPHABET_REPLAY',len(mods),'modules')
