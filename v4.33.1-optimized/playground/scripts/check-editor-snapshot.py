#!/usr/bin/env python3
"""LSP edit/Infoview regression probe. Usage: LABEL [SERVER ARGS...]. No source edits."""
import json, os, sys
from pathlib import Path
project = Path(__file__).resolve().parent.parent
sys.path.insert(0,str(project/'.lake/toolchains/lean-optimizations/code/benchmarks/interactive'))
from lspbench import LeanLsp
out=project/'.lake/infoview-investigation'/sys.argv[1]
out.mkdir(parents=True,exist_ok=True)
c=LeanLsp(sys.argv[2:] or ['lake','serve'],project,dict(os.environ),out)
uri=(project/'Playground/Scratch.lean').as_uri()
original=(project/'Playground/Scratch.lean').read_text()
results=[]
def check(text,version,expect_error=False):
    t=c.now()
    if version==1:
        c.notify('textDocument/didOpen',{'textDocument':{'uri':uri,'languageId':'lean','version':version,'text':text},'dependencyBuildMode':'never'})
    else:
        c.notify('textDocument/didChange',{'textDocument':{'uri':uri,'version':version},'contentChanges':[{'text':text}]})
    done=c.wait_progress_done(uri,version,120,min_t=t)
    assert done is not None,('progress timeout',version)
    assert c.wait_diag_version(uri,version,20) is not None,('diagnostic timeout',version)
    diagnostics=c.diags[uri]['diagnostics']
    errors=[d for d in diagnostics if d.get('severity')==1]
    assert bool(errors)==expect_error,(version,diagnostics)
    row={'version':version,'seconds':done-t,'diagnostics':diagnostics}
    if not expect_error:
        line=next(i for i,s in enumerate(text.splitlines()) if s.strip()=='linarith')
        params={'textDocument':{'uri':uri},'position':{'line':line,'character':2}}
        goal=c.request('$/lean/plainGoal',params)
        assert 'error' not in goal and 'x + y' in json.dumps(goal),goal
        session=c.request('$/lean/rpc/connect',{'uri':uri})['result']['sessionId']
        interactive=c.request('$/lean/rpc/call',{**params,'sessionId':session,'method':'Lean.Widget.getInteractiveGoals','params':params})
        assert 'error' not in interactive and interactive.get('result'),interactive
        def render(value):
            if isinstance(value,dict):
                if 'text' in value: return value['text']
                if 'tag' in value: return render(value['tag'][1])
                if 'append' in value: return render(value['append'])
            if isinstance(value,list): return ''.join(map(render,value))
            return ''
        assert 'x + y' in render(interactive['result']['goals'][0]['type']),interactive
        row.update(plainGoal=goal['result'],interactiveGoals=interactive['result'])
    results.append(row)
    (out/'checks.json').write_text(json.dumps(results,indent=2))
    print(json.dumps({'version':version,'seconds':row['seconds'],'errors':len(errors)}),flush=True)
try:
    c.request('initialize',{'processId':os.getpid(),'rootUri':project.as_uri(),'capabilities':{'textDocument':{'publishDiagnostics':{'versionSupport':True}}},'initializationOptions':{'hasWidgets':True,'editDelay':0}})
    c.notify('initialized',{})
    check(original,1)
    check(original+'\nexample : False := by trivial\n',2,True)
    check(original,3)
    check(original.replace('import Mathlib','import MissingSnapshotRegressionModule'),4,True)
    check(original,5)
    check('-- moved header for snapshot fallback\n'+original,6)
    print('All edit and Infoview RPC checks passed.',flush=True)
finally:
    c.close()
