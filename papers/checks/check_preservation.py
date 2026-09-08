from pathlib import Path
import re,json,hashlib
base=Path(__file__).resolve().parents[1]
block_re=re.compile(r'\\\[(.*?)\\\]|\$\$(.*?)\$\$',re.S)
def displays(s):return [a or b for a,b in block_re.findall(s)]
def norm(s):return re.sub(r'\s+','',s)
def numbered(s):
 out={}
 for b in displays(s):
  for tag in re.findall(r'\\tag\{([^}]+)\}',b):
   assert tag not in out,tag
   out[tag]=norm(b)
 return out
def prose(s):
 s=block_re.sub(' ',s)
 s=re.sub(r'\\\(.*?\\\)',' ',s,flags=re.S)
 s=re.sub(r'(?<!\\)\$(?!\$).*?(?<!\\)\$',' ',s,flags=re.S)
 s=re.sub(r'^---\n.*?\n---\n',' ',s,flags=re.S)
 s=re.sub(r'^\\.*$',' ',s,flags=re.M)
 return len(re.findall(r"\b[\w]+(?:[’'-][\w]+)*\b",s))
results={}
for stem,orig in [('kakeya_paper_i',base/'originals/kakeya_paper_i.md'),('kakeya_combined',base/'originals/kakeya_combined.md')]:
 rev=base/f'{stem}.md'; a=orig.read_text();b=rev.read_text(); na=numbered(a);nb=numbered(b)
 changes=[{'tag':k,'old':na[k],'new':nb[k]} for k in na.keys()&nb.keys() if na[k]!=nb[k]]
 result={'original_display_blocks':len(displays(a)),'revised_display_blocks':len(displays(b)),'original_numbered_displays':len(na),'revised_numbered_displays':len(nb),'removed_tags':sorted(na.keys()-nb.keys()),'added_tags':sorted(nb.keys()-na.keys()),'changed_numbered_displays':changes,'original_prose_words':prose(a),'revised_prose_words':prose(b),'original_whitespace_tokens':len(a.split()),'revised_whitespace_tokens':len(b.split()),'original_sha256':hashlib.sha256(orig.read_bytes()).hexdigest(),'revised_sha256':hashlib.sha256(rev.read_bytes()).hexdigest()}
 ids=lambda s: re.findall(r'\*\*(?:Theorem|Lemma|Corollary|Proposition)\s+([A-Z0-9]+\.[0-9]+)',s)
 result['statement_numbers_preserved']=ids(a)==ids(b)
 result['all_original_displays_preserved']=all(norm(d) in {norm(x) for x in displays(b)} for d in displays(a))
 results[stem]=result
 assert not result['removed_tags'] and not result['added_tags']
 assert result['statement_numbers_preserved']
 assert not changes,changes
(base/'checks/preservation_results.json').write_text(json.dumps(results,indent=2)+'\n')
print(json.dumps(results,indent=2))
