#!/usr/bin/env python3
"""Record LSP opening and goal latency; run from this playground.

Usage: python3 scripts/probe-editor.py LABEL [direct]
Uses the pinned optimization repository's stdlib-only LSP test client.
Set LEAN_EDITOR_SETUP_CACHE=0 for an uncached baseline.
"""
import sys, os, json, time, subprocess
from pathlib import Path
p=Path(__file__).resolve().parent.parent
sys.path.insert(0,str(p/'.lake/toolchains/lean-optimizations/code/benchmarks/interactive'))
from lspbench import LeanLsp
label=sys.argv[1]
out=p/'.lake/infoview-investigation'/label
out.mkdir(exist_ok=True)
env=dict(os.environ)
env.pop('LEAN_NUM_THREADS',None)
cmd=['lake','serve']
if len(sys.argv)>2 and sys.argv[2]=='direct':
    env=json.loads(subprocess.check_output(['lake','env','python3','-c','import os,json; print(json.dumps(dict(os.environ)))']))
    if os.environ.get('LAKE'): env['LAKE']=os.environ['LAKE']
    cmd=[str(p/'.lake/toolchains/lean4/build/release/stage2/bin/lean'),'--server',str(p)]
c=LeanLsp(cmd,p,env,out)
uri=(p/'Playground/Scratch.lean').as_uri()
try:
    c.request('initialize',{'processId':os.getpid(),'rootUri':p.as_uri(),'capabilities':{'textDocument':{'publishDiagnostics':{'versionSupport':True}}},'initializationOptions':{'hasWidgets':True,'editDelay':0}})
    c.notify('initialized',{})
    t=c.now()
    c.notify('textDocument/didOpen',{'textDocument':{'uri':uri,'languageId':'lean','version':1,'text':(p/'Playground/Scratch.lean').read_text()},'dependencyBuildMode':'never'})
    done=c.wait_progress_done(uri,1,120,min_t=t)
    assert done is not None and not c.progress[uri].get('fatal'),c.diags
    g=c.now()
    goal=c.request('$/lean/plainGoal',{'textDocument':{'uri':uri},'position':{'line':3,'character':2}})
    r=dict(initialize_s=t,open_s=done-t,goal_s=c.now()-g,goal=goal,diagnostics=c.diags)
    assert 'x + y' in json.dumps(goal),goal
    assert not any(d.get('severity')==1 for x in c.diags.values() for d in x['diagnostics']),c.diags
    (out/'result.json').write_text(json.dumps(r,indent=2))
    print(json.dumps(r),flush=True)
finally:
    c.close()
