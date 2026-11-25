import {readFileSync, writeFileSync, mkdtempSync, rmSync} from 'node:fs';
import {createHash} from 'node:crypto';
import {spawnSync} from 'node:child_process';
import {join} from 'node:path';
const binary=process.argv[2];
const python=process.argv[3];
const observer=process.argv[4];
const sha256=bytes=>createHash('sha256').update(bytes).digest('hex');
const observe=stage=>{
  const r=spawnSync(python,[observer,String(process.pid)],{encoding:'utf8'});
  if(r.status!==0) throw Error('observer failed');
  process.stdout.write(JSON.stringify({stage,...JSON.parse(r.stdout)})+'\n');
};
observe('before');
const first=sha256(readFileSync(binary));
observe('first_hash_then_build');
const fixedFault=()=>{
  if(sha256(readFileSync(binary))!==first) return 'changed';
  for(const file of ['lean/lean-toolchain','lean/lakefile.toml','lean/lake-manifest.json']) sha256(readFileSync(file));
  return null;
};
if(fixedFault()) throw Error('binary changed');
const directory=mkdtempSync('/tmp/oec/pequalnp-pilot-45/node-gc-probe/statement-');
process.on('exit',()=>rmSync(directory,{recursive:true,force:true}));
writeFileSync(join(directory,'statement.lean'),'True',{mode:0o400});
observe('second_hash_then_verify');
