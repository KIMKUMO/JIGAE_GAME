(function(){
'use strict';
const $ = id => document.getElementById(id);

// ---------------------------------------------------------------- utils
function mulberry32(a){return function(){a|=0;a=a+0x6D2B79F5|0;let t=Math.imul(a^a>>>15,1|a);t=t+Math.imul(t^t>>>7,61|t)^t;return((t^t>>>14)>>>0)/4294967296;};}
const rand = mulberry32(20261126);
function hash2(ix,iz){let h=(Math.imul(ix|0,374761393)+Math.imul(iz|0,668265263))|0;h=Math.imul(h^(h>>>13),1274126177);h^=h>>>16;return (h>>>0)/4294967295;}
function vnoise(x,z){const ix=Math.floor(x),iz=Math.floor(z),fx=x-ix,fz=z-iz,ux=fx*fx*(3-2*fx),uz=fz*fz*(3-2*fz);
  const a=hash2(ix,iz),b=hash2(ix+1,iz),c=hash2(ix,iz+1),d=hash2(ix+1,iz+1);
  return (a+(b-a)*ux)*(1-uz)+(c+(d-c)*ux)*uz;}
function fbm(x,z){return (vnoise(x,z)-.5)+(vnoise(x*2.1+5.3,z*2.1+9.1)-.5)*.5+(vnoise(x*4.3+13.7,z*4.3+2.9)-.5)*.25;}
const clamp=(v,a,b)=>v<a?a:v>b?b:v;
const lerp=(a,b,t)=>a+(b-a)*t;
function smoothstep(a,b,x){const t=clamp((x-a)/(b-a),0,1);return t*t*(3-2*t);}

// ---------------------------------------------------------------- world constants
// No roads. The mountain has ridges, gullies and bands of cliffs. A faint, broken old trail
// (worn grass, hiking ribbons on trees, small cairns) threads through the gaps in the cliffs,
// but the player has to spot it and pick a way up on their own.
const HALF=420, SEG=420, CELL=2*HALF/SEG, VN=SEG+1;
const H=170, SIG=165;
const START_R=335, THETA0=Math.PI*0.25;
const SUMMIT_R=7;
const TRAIL_W=2.2;           // half-width of the worn old trail

function mtnBase(r){return H*Math.exp(-(r*r)/(SIG*SIG));}
function roughAt(x,z){const r=Math.hypot(x,z);return fbm(x/40,z/40)*9*Math.min(1,r/60)+fbm(x/9,z/9)*1.6*Math.min(1,r/25);}
function ridgesAt(x,z,r){
  const th=Math.atan2(z,x),w=fbm(x/90,z/90)*1.4;
  const amp=16*smoothstep(30,120,r)*(1-smoothstep(250,360,r));
  return (0.35-Math.abs(Math.sin(2.5*th+w)))*amp;   // narrow spurs, broad gullies
}
function baseHeight(x,z){
  const r=Math.hypot(x,z);
  let h=mtnBase(r)+ridgesAt(x,z,r)+roughAt(x,z);
  h=lerp(H,h,smoothstep(10,24,r));
  h*=1-smoothstep(370,415,r);
  return h;
}

// ---------------------------------------------------------------- hidden old trail
function targetGrade(s){
  const ph=(s%80)/80,k=smoothstep(0,0.12,ph)*(1-smoothstep(0.45,0.57,ph)),prog=clamp(s/1100,0,1);
  return lerp(lerp(0.04,0.08,prog),lerp(0.16,0.28,prog),k);
}
function guideHeight(x,z){const r=Math.hypot(x,z);return mtnBase(r)+ridgesAt(x,z,r);}
function trailWiggle(s){return 0.5*Math.sin(s/14)+0.3*Math.sin(s/5.3+1);}
const _px=[],_pz=[];
{
  let x=START_R*Math.cos(THETA0),z=START_R*Math.sin(THETA0),s=0;const ds=0.5,e=1.5;_px.push(x);_pz.push(z);
  for(let n=0;n<9000;n++){
    const r=Math.hypot(x,z);if(r<8)break;
    // steer on the large-scale shape (mountain + spurs); small bumps would trap it on little hillocks
    let ux=(guideHeight(x+e,z)-guideHeight(x-e,z))/(2*e),uz=(guideHeight(x,z+e)-guideHeight(x,z-e))/(2*e);
    const sl=Math.hypot(ux,uz)||1e-4;ux/=sl;uz/=sl;
    const gw=Math.min(1,sl/0.15);ux=ux*gw-x/r*0.6;uz=uz*gw-z/r*0.6;const ul=Math.hypot(ux,uz);ux/=ul;uz/=ul;   // lean toward the summit
    const tx=uz,tz=-ux;
    const c=clamp(targetGrade(s)/Math.max(sl,1e-4),0,1);
    let a=Math.acos(c)+trailWiggle(s);
    a=Math.max(a,Math.acos(Math.min(1,c*1.3+0.02)));a=Math.min(a,Math.PI/2+0.05);
    x+=(ux*Math.cos(a)+tx*Math.sin(a))*ds;z+=(uz*Math.cos(a)+tz*Math.sin(a))*ds;s+=ds;
    _px.push(x);_pz.push(z);
  }
}
const PN=_px.length;
const PX=Float32Array.from(_px),PZ=Float32Array.from(_pz),PY=new Float32Array(PN),PS=new Float32Array(PN);
PS[0]=0;for(let i=1;i<PN;i++){PS[i]=PS[i-1]+Math.hypot(PX[i]-PX[i-1],PZ[i]-PZ[i-1]);}
const PATH_LEN=PS[PN-1];
const BC=8, BN=Math.ceil(2*HALF/BC);
const buckets=Array.from({length:BN*BN},()=>[]);
for(let i=0;i<PN;i++){const bx=clamp(Math.floor((PX[i]+HALF)/BC),0,BN-1),bz=clamp(Math.floor((PZ[i]+HALF)/BC),0,BN-1);buckets[bz*BN+bx].push(i);}
function nearestPath(x,z,m){
  const bx=Math.floor((x+HALF)/BC),bz=Math.floor((z+HALF)/BC);let best=-1,bd=Infinity;
  for(let dz=-m;dz<=m;dz++){const cz=bz+dz;if(cz<0||cz>=BN)continue;
    for(let dx=-m;dx<=m;dx++){const cx=bx+dx;if(cx<0||cx>=BN)continue;
      const L=buckets[cz*BN+cx];for(let k=0;k<L.length;k++){const i=L[k],ddx=PX[i]-x,ddz=PZ[i]-z,d=ddx*ddx+ddz*ddz;if(d<bd){bd=d;best=i;}}}}
  return best<0?null:{i:best,d:Math.sqrt(bd)};
}

// ---------------------------------------------------------------- cliff bands
// Each band is a ring of near-vertical rock you cannot walk up. It opens into a gentle ramp
// where the old trail crosses, plus one more random gap somewhere else.
const angDist=(a,b)=>Math.abs(Math.atan2(Math.sin(a-b),Math.cos(a-b)));
function cliffEdge(c,th){return c.rc+(vnoise(Math.cos(th)*3+c.rc,Math.sin(th)*3)-0.5)*16;}
const CLIFFS=[{rc:255,hc:8},{rc:170,hc:12},{rc:100,hc:10},{rc:48,hc:6}].map(c=>{
  // open a gap wherever the old trail meets the cliff line (clusters of nearby trail points)
  const angs=[];
  for(let i=0;i<PN;i+=2){const r=Math.hypot(PX[i],PZ[i]),th=Math.atan2(PZ[i],PX[i]);if(Math.abs(r-cliffEdge(c,th))<6)angs.push(th);}
  angs.sort((p,q)=>p-q);
  c.gaps=[];
  let start=0;
  for(let k=1;k<=angs.length;k++){
    if(k===angs.length||angs[k]-angs[k-1]>0.06){
      const a0=angs[start],a1=angs[k-1];c.gaps.push({a:(a0+a1)/2,hw:(a1-a0)/2+26/c.rc});start=k;
    }
  }
  c.gaps.push({a:rand()*Math.PI*2,hw:14/c.rc});   // one more way through, somewhere else
  return c;
});
function cliffAdd(x,z){
  const r=Math.hypot(x,z),th=Math.atan2(z,x);let add=0;
  for(const c of CLIFFS){
    let g=0;for(const gp of c.gaps)g=Math.max(g,1-smoothstep(gp.hw,gp.hw+14/c.rc,angDist(th,gp.a)));
    const w=lerp(2.2,30,g),rc=cliffEdge(c,th);
    add+=c.hc*(1-smoothstep(rc-w,rc+w,r));
  }
  return add;
}
const SUMMIT_H=H+CLIFFS.reduce((s,c)=>s+c.hc,0);
const ALT0=420, ALT_SCALE=(980-420)/SUMMIT_H;
{
  const raw=new Float32Array(PN);for(let i=0;i<PN;i++)raw[i]=baseHeight(PX[i],PZ[i])+cliffAdd(PX[i],PZ[i]);
  const W=12;for(let i=0;i<PN;i++){let s=0,n=0;for(let k=-W;k<=W;k++){s+=raw[clamp(i+k,0,PN-1)];n++;}PY[i]=s/n;}
}

// ---------------------------------------------------------------- heightfield
const HF=new Float32Array(VN*VN), PW=new Float32Array(VN*VN);
for(let iz=0;iz<VN;iz++)for(let ix=0;ix<VN;ix++){
  const x=-HALF+ix*CELL,z=-HALF+iz*CELL;let h=baseHeight(x,z)+cliffAdd(x,z),pw=0;
  const np=nearestPath(x,z,1);
  if(np&&np.d<4){
    h=lerp(h,PY[np.i],0.35*(1-smoothstep(1.5,3.8,np.d)));     // a slightly worn bench, not a road
    const patch=smoothstep(0.32,0.58,vnoise(PS[np.i]/9,4.2));  // the trail fades in and out
    pw=(1-smoothstep(0.6,TRAIL_W+0.6,np.d))*lerp(0.12,0.6,patch);
  }
  HF[iz*VN+ix]=h;PW[iz*VN+ix]=pw;
}
function groundH(x,z){
  const fx=(x+HALF)/CELL,fz=(z+HALF)/CELL;
  if(fx<0||fz<0||fx>=SEG||fz>=SEG)return 0;
  const ix=Math.floor(fx),iz=Math.floor(fz),tx=fx-ix,tz=fz-iz,i=iz*VN+ix;
  return lerp(lerp(HF[i],HF[i+1],tx),lerp(HF[i+VN],HF[i+VN+1],tx),tz);
}
const _n=new THREE.Vector3();
function groundN(x,z,out){const e=0.5;out.set(groundH(x-e,z)-groundH(x+e,z),2*e,groundH(x,z-e)-groundH(x,z+e)).normalize();return out;}
function slopeAt(x,z){const e=0.6;return Math.hypot(groundH(x+e,z)-groundH(x-e,z),groundH(x,z+e)-groundH(x,z-e))/(2*e);}

// ---------------------------------------------------------------- renderer / scene
const canvas=$('game');
const renderer=new THREE.WebGLRenderer({canvas,antialias:true});
renderer.setPixelRatio(Math.min(window.devicePixelRatio||1,1.75));
renderer.setSize(innerWidth,innerHeight,false);
renderer.shadowMap.enabled=true;renderer.shadowMap.type=THREE.PCFSoftShadowMap;
const scene=new THREE.Scene();
const FOG=0xe6d3b0;
scene.background=new THREE.Color(FOG);
scene.fog=new THREE.Fog(FOG,220,1500);
const camera=new THREE.PerspectiveCamera(58,innerWidth/innerHeight,0.1,3200);

scene.add(new THREE.HemisphereLight(0xd6e6ff,0x5d4a30,0.72));
const sun=new THREE.DirectionalLight(0xffe7c4,0.9);
sun.castShadow=true;sun.shadow.mapSize.set(2048,2048);
const sc=sun.shadow.camera;sc.left=-34;sc.right=34;sc.top=34;sc.bottom=-34;sc.near=1;sc.far=260;
sun.shadow.bias=-0.0008;
scene.add(sun);scene.add(sun.target);
const SUN_OFF=new THREE.Vector3(-70,95,55);

// sky dome
{
  const R0=2400,g=new THREE.SphereGeometry(R0,32,16),pos=g.attributes.position,cols=[];
  const top=new THREE.Color(0x5f97cf),hor=new THREE.Color(0xf2d6a8),c=new THREE.Color();
  for(let i=0;i<pos.count;i++){const y=pos.getY(i)/R0;c.copy(hor).lerp(top,Math.pow(clamp(y,0,1),0.55));cols.push(c.r,c.g,c.b);}
  g.setAttribute('color',new THREE.Float32BufferAttribute(cols,3));
  scene.add(new THREE.Mesh(g,new THREE.MeshBasicMaterial({vertexColors:true,side:THREE.BackSide,fog:false,depthWrite:false})));
  const sunDisc=new THREE.Mesh(new THREE.CircleGeometry(80,32),new THREE.MeshBasicMaterial({color:0xfff2d6,fog:false}));
  sunDisc.position.copy(SUN_OFF).normalize().multiplyScalar(2300);sunDisc.lookAt(0,0,0);scene.add(sunDisc);
}

function lam(c,o){return new THREE.MeshLambertMaterial(Object.assign({color:c},o||{}));}

// terrain
{
  const g=new THREE.PlaneGeometry(2*HALF,2*HALF,SEG,SEG);g.rotateX(-Math.PI/2);
  const pos=g.attributes.position,cols=new Float32Array(pos.count*3);
  const cG1=new THREE.Color(0x667f3b),cG2=new THREE.Color(0x9a8a45),cG3=new THREE.Color(0x7d6a3a),cRock=new THREE.Color(0x8a8070),cCliff=new THREE.Color(0x6f675c),cWorn=new THREE.Color(0xa58a58),c=new THREE.Color();
  for(let iz=0;iz<VN;iz++)for(let ix=0;ix<VN;ix++){
    const i=iz*VN+ix,x=-HALF+ix*CELL,z=-HALF+iz*CELL;pos.setY(i,HF[i]);
    const hx=HF[iz*VN+Math.min(ix+1,SEG)]-HF[iz*VN+Math.max(ix-1,0)],hz=HF[Math.min(iz+1,SEG)*VN+ix]-HF[Math.max(iz-1,0)*VN+ix];
    const slope=Math.hypot(hx,hz)/(2*CELL);
    const n1=vnoise(x/14,z/14),n2=vnoise(x/5+40,z/5+40);
    c.copy(cG1).lerp(cG2,n1).lerp(cG3,n2*0.45);
    c.lerp(cRock,smoothstep(0.6,1.0,slope)*0.85);
    c.lerp(cCliff,smoothstep(1.0,1.6,slope));
    c.lerp(cRock,smoothstep(SUMMIT_H*0.72,SUMMIT_H*0.95,HF[i])*0.45);
    c.lerp(cWorn,PW[i]);
    cols[i*3]=c.r;cols[i*3+1]=c.g;cols[i*3+2]=c.b;
  }
  g.setAttribute('color',new THREE.BufferAttribute(cols,3));g.computeVertexNormals();
  const terrain=new THREE.Mesh(g,lam(0xffffff,{vertexColors:true}));terrain.receiveShadow=true;scene.add(terrain);
  const ring=new THREE.Mesh(new THREE.RingGeometry(HALF*1.414,4000,64,1),lam(0x6c7a3c));ring.rotation.x=-Math.PI/2;scene.add(ring);
}

// trees, rocks, hiking ribbons
const dummy=new THREE.Object3D();
const blockers=[];              // trunks and big rocks the player bumps into
const BLK=6, BLN=Math.ceil(2*HALF/BLK), blockGrid=Array.from({length:BLN*BLN},()=>[]);
function addBlocker(x,z,r){const o={x,z,r};blockers.push(o);const bx=clamp(Math.floor((x+HALF)/BLK),0,BLN-1),bz=clamp(Math.floor((z+HALF)/BLK),0,BLN-1);blockGrid[bz*BLN+bx].push(o);}
{
  const pines=[],leafy=[],rocks=[],ribbons=[];
  for(let k=0;k<22000&&(pines.length+leafy.length)<5200;k++){
    const a=rand()*Math.PI*2,r=16+Math.sqrt(rand())*380;const x=Math.cos(a)*r,z=Math.sin(a)*r;
    const np=nearestPath(x,z,1);if(np&&np.d<3.2)continue;
    const y=groundH(x,z);if(groundN(x,z,_n).y<0.72)continue;
    if(vnoise(x/34+7,z/34+3)<0.3)continue; // clearings
    if(y>SUMMIT_H*0.78&&rand()<0.6)continue;
    const s=(0.75+rand()*0.75)*(y>SUMMIT_H*0.75?0.7:1);
    const t={x,y,z,s,rot:rand()*6.28};
    (rand()<(y>SUMMIT_H*0.5?0.75:0.5)?pines:leafy).push(t);
    addBlocker(x,z,0.22*s+0.08);
    // 산악회 리본: hiking-club ribbons tied on trees beside the old trail
    if(np&&np.d<7&&rand()<0.35){const dx=PX[np.i]-x,dz=PZ[np.i]-z,dl=Math.hypot(dx,dz)||1;ribbons.push({x:x+dx/dl*0.26*s,z:z+dz/dl*0.26*s,y:y+0.8*s,rot:Math.atan2(dx,dz)});}
  }
  for(let k=0;k<900;k++){const a=rand()*Math.PI*2,r=10+Math.sqrt(rand())*390,x=Math.cos(a)*r,z=Math.sin(a)*r;const np=nearestPath(x,z,1);if(np&&np.d<3.5)continue;
    const steep=slopeAt(x,z)>0.9;if(!steep&&rand()<0.55)continue;                     // rocks gather on cliffs
    const s=0.4+rand()*(steep?2.2:1.3);rocks.push({x,y:groundH(x,z),z,s,rot:rand()*6.28});if(s>0.9)addBlocker(x,z,s*0.55);}
  const trunkG=new THREE.CylinderGeometry(0.14,0.22,1,5);trunkG.translate(0,0.5,0);
  const pineLo=new THREE.ConeGeometry(1.5,2.6,7);pineLo.translate(0,2.3,0);
  const pineHi=new THREE.ConeGeometry(1.05,2.1,7);pineHi.translate(0,3.6,0);
  const leafG=new THREE.IcosahedronGeometry(1.55,0);leafG.translate(0,2.6,0);
  const rockG=new THREE.DodecahedronGeometry(0.6,0);
  function inst(geo,mat,list,fn,shadow){const m=new THREE.InstancedMesh(geo,mat,Math.max(1,list.length));m.count=list.length;m.castShadow=shadow!==false;m.receiveShadow=true;const c=new THREE.Color();
    list.forEach((t,i)=>{fn(t,dummy,c);dummy.updateMatrix();m.setMatrixAt(i,dummy.matrix);m.setColorAt(i,c);});m.instanceMatrix.needsUpdate=true;if(m.instanceColor)m.instanceColor.needsUpdate=true;scene.add(m);return m;}
  const all=pines.concat(leafy);
  inst(trunkG,lam(0xffffff),all,(t,d,c)=>{d.position.set(t.x,t.y-0.1,t.z);d.rotation.set(0,t.rot,0);d.scale.set(t.s,t.s*1.9,t.s);c.setHex(0x5e4026);});
  const pinePal=[0x2f5a37,0x3a6a3c,0x2a4d33,0x46703f];
  inst(pineLo,lam(0xffffff,{flatShading:true}),pines,(t,d,c)=>{d.position.set(t.x,t.y,t.z);d.rotation.set(0,t.rot,0);d.scale.setScalar(t.s);c.setHex(pinePal[(t.rot*10|0)%4]);});
  inst(pineHi,lam(0xffffff,{flatShading:true}),pines,(t,d,c)=>{d.position.set(t.x,t.y,t.z);d.rotation.set(0,t.rot,0);d.scale.setScalar(t.s);c.setHex(pinePal[(t.rot*10+1|0)%4]);});
  const autumn=[0xc8452b,0xe07a2e,0xe8b43a,0xb5392a,0xd8962f,0x9a8a3c];
  inst(leafG,lam(0xffffff,{flatShading:true}),leafy,(t,d,c)=>{d.position.set(t.x,t.y,t.z);d.rotation.set(t.rot,t.rot*2,0);d.scale.set(t.s,t.s*1.1,t.s);c.setHex(autumn[(t.rot*13|0)%autumn.length]);});
  inst(rockG,lam(0xffffff,{flatShading:true}),rocks,(t,d,c)=>{d.position.set(t.x,t.y,t.z);d.rotation.set(t.rot,t.rot*1.7,t.rot*.5);d.scale.set(t.s,t.s*0.7,t.s*1.1);c.setRGB(0.5+Math.min(t.s,2)*0.04,0.48+Math.min(t.s,2)*0.03,0.44);});
  const ribPal=[0xe23b2e,0xf2c230,0x2f7fd8,0xf0f0f0];
  inst(new THREE.BoxGeometry(0.09,0.55,0.015),new THREE.MeshBasicMaterial({color:0xffffff}),ribbons,(t,d,c)=>{d.position.set(t.x,t.y,t.z);d.rotation.set(0.15,t.rot,0.1);d.scale.setScalar(1);c.setHex(ribPal[(t.rot*7|0)&3]);},false);
}

// far ridges
{
  const g=new THREE.ConeGeometry(1,1,6);
  const m=new THREE.InstancedMesh(g,lam(0x7f8c98,{flatShading:true}),40);
  for(let i=0;i<40;i++){const a=i/40*Math.PI*2+rand()*0.12,r=950+rand()*400,s=150+rand()*220;dummy.position.set(Math.cos(a)*r,s*0.38-10,Math.sin(a)*r);dummy.rotation.set(0,rand()*3,0);dummy.scale.set(s*1.3,s*0.8,s*1.2);dummy.updateMatrix();m.setMatrixAt(i,dummy.matrix);}
  scene.add(m);
}

// stones on the old trail, and small cairns (돌무더기) people left beside it
const bumps=[];
{
  const cairnStones=[];
  let i=Math.floor(6/0.5),nextCairn=60;
  while(i<PN*0.98){
    const t=PS[i]/PATH_LEN;
    const a=Math.max(0,i-1),b=Math.min(PN-1,i+1);let tx=PX[b]-PX[a],tz=PZ[b]-PZ[a];const tl=Math.hypot(tx,tz)||1;
    const off=(rand()*2-1)*1.1;const x=PX[i]-tz/tl*off,z=PZ[i]+tx/tl*off;
    bumps.push({x,z,y:groundH(x,z),s:0.22+rand()*0.16,cd:0});
    if(PS[i]>nextCairn){nextCairn=PS[i]+70+rand()*40;const cx=PX[i]+tz/tl*2.6,cz=PZ[i]-tx/tl*2.6;let y=groundH(cx,cz);
      for(let k=0;k<4;k++){const s=0.34-k*0.06;cairnStones.push({x:cx+(rand()-.5)*0.08,y:y+s*0.4,z:cz+(rand()-.5)*0.08,s});y+=s*0.7;}}
    i+=Math.floor((lerp(26,10,t)+rand()*10)/0.5);
  }
  const all=bumps.map(b=>({x:b.x,y:b.y+0.02,z:b.z,s:b.s,flat:0.6})).concat(cairnStones.map(c=>({x:c.x,y:c.y,z:c.z,s:c.s,flat:0.55})));
  const m=new THREE.InstancedMesh(new THREE.DodecahedronGeometry(1,0),lam(0x8c8577,{flatShading:true}),all.length);m.castShadow=true;m.receiveShadow=true;
  all.forEach((b,k)=>{dummy.position.set(b.x,b.y,b.z);dummy.rotation.set(k,k*2.3,k*.7);dummy.scale.set(b.s*1.2,b.s*b.flat,b.s);dummy.updateMatrix();m.setMatrixAt(k,dummy.matrix);});
  scene.add(m);
}

// tree roots lying across the steep stretches of the old trail
const roots=[];
{
  const rootMat=lam(0x5b3b20);
  let i=Math.floor(30/0.5);
  while(i<PN-40){
    const a=Math.max(0,i-12),b=Math.min(PN-1,i+12),gr=(PY[b]-PY[a])/(PS[b]-PS[a]+1e-6);
    if(gr>0.15){
      let tx=PX[b]-PX[a],tz=PZ[b]-PZ[a];const tl=Math.hypot(tx,tz)||1;tx/=tl;tz/=tl;
      const half=1.7,x=PX[i],z=PZ[i];
      const m=new THREE.Mesh(new THREE.CylinderGeometry(0.08,0.12,half*2,6),rootMat);
      m.rotation.set(0,Math.atan2(-tx,-tz),Math.PI/2);m.position.set(x,groundH(x,z)+0.06,z);m.castShadow=true;m.receiveShadow=true;scene.add(m);
      roots.push({x,z,tx,tz,half,cd:0});
      i+=Math.floor((9+rand()*10)/0.5);
    }else i+=Math.floor(3/0.5);
  }
}

// signpost at the foot of the mountain
const signs=[];
function makeSign(l1,l2,at,side){
  const cv=document.createElement('canvas');cv.width=512;cv.height=256;
  const tex=new THREE.CanvasTexture(cv);
  const draw=()=>{const g=cv.getContext('2d');g.fillStyle='#6e4626';g.fillRect(0,0,512,256);
    g.strokeStyle='rgba(0,0,0,.18)';g.lineWidth=3;for(let y=18;y<256;y+=22){g.beginPath();g.moveTo(0,y+Math.sin(y)*4);g.bezierCurveTo(170,y-6,340,y+8,512,y);g.stroke();}
    g.strokeStyle='#4a2d16';g.lineWidth=14;g.strokeRect(7,7,498,242);
    g.fillStyle='#f3ecdc';g.textAlign='center';g.textBaseline='middle';
    g.font='86px "Black Han Sans", "Malgun Gothic", sans-serif';g.fillText(l1,256,104);
    g.font='600 40px "IBM Plex Sans KR", "Malgun Gothic", sans-serif';g.fillStyle='#ffcf7a';g.fillText(l2,256,192);tex.needsUpdate=true;};
  draw();signs.push(draw);
  const grp=new THREE.Group();
  const post=new THREE.Mesh(new THREE.CylinderGeometry(0.07,0.08,2.2,6),lam(0x5a3a20));post.position.y=1.1;post.castShadow=true;grp.add(post);
  const wood=lam(0x6e4626),face=new THREE.MeshLambertMaterial({map:tex});
  const board=new THREE.Mesh(new THREE.BoxGeometry(1.6,0.8,0.08),[wood,wood,wood,wood,face,face]);board.position.y=1.85;board.castShadow=true;grp.add(board);
  const i=clamp(at,1,PN-2);let tx=PX[i+1]-PX[i-1],tz=PZ[i+1]-PZ[i-1];const tl=Math.hypot(tx,tz);tx/=tl;tz/=tl;
  const x=PX[i]-tz*side,z=PZ[i]+tx*side;grp.position.set(x,groundH(x,z),z);
  grp.rotation.y=Math.atan2(tx,tz)+Math.PI;scene.add(grp);
}
makeSign('소리봉','길 없음 · 리본을 찾아보세요',14,3.2);
if(document.fonts&&document.fonts.ready)document.fonts.ready.then(()=>signs.forEach(f=>f()));

// summit cairn + a tall flag you can see from the foot of the mountain
let summitFlag=null;
{
  const g=new THREE.Group();const sm=lam(0x9a9284,{flatShading:true});
  let y=0;for(let k=0;k<7;k++){const s=0.75-k*0.08;const st=new THREE.Mesh(new THREE.DodecahedronGeometry(s,0),sm);st.scale.set(1,0.55,1);st.position.set((rand()-.5)*.15,y+s*0.45,(rand()-.5)*.15);st.rotation.y=k;st.castShadow=true;g.add(st);y+=s*0.8;}
  const pole=new THREE.Mesh(new THREE.CylinderGeometry(0.07,0.09,9,6),lam(0x5a3a20));pole.position.set(1.6,4.5,0);pole.castShadow=true;g.add(pole);
  summitFlag=new THREE.Mesh(new THREE.PlaneGeometry(3,1.8,10,1),new THREE.MeshBasicMaterial({color:0xffb23e,side:THREE.DoubleSide}));
  summitFlag.position.set(3.1,8.0,0);g.add(summitFlag);
  g.position.set(0,groundH(0,0),0);scene.add(g);
}

// ---------------------------------------------------------------- characters
function box(w,h,d,m){const o=new THREE.Mesh(new THREE.BoxGeometry(w,h,d),m);o.castShadow=true;return o;}
function cyl(rt,rb,h,m,seg){const o=new THREE.Mesh(new THREE.CylinderGeometry(rt,rb,h,seg||8),m);o.castShadow=true;return o;}
const M={skin:lam(0xe2b48c),white:lam(0xece3cc),pants:lam(0x4a586b),wood:lam(0x8b5a2b),woodDark:lam(0x5e3c1e),straw:lam(0xd6b25e),dark:lam(0x2b2520)};

const player=new THREE.Group();scene.add(player);
const hips=new THREE.Group();hips.position.y=0.92;player.add(hips);
const legs=[];
for(const sx of [-1,1]){const g=new THREE.Group();g.position.set(0.11*sx,0,0);const l=cyl(0.075,0.065,0.86,M.pants);l.position.y=-0.43;g.add(l);const f=box(0.12,0.08,0.24,M.dark);f.position.set(0,-0.88,0.05);g.add(f);hips.add(g);legs.push(g);}
const torso=new THREE.Group();hips.add(torso);
{const c=cyl(0.2,0.25,0.64,M.white);c.position.y=0.32;torso.add(c);
 const b=cyl(0.255,0.255,0.07,M.pants);b.position.y=0.04;torso.add(b);
 const hd=new THREE.Mesh(new THREE.SphereGeometry(0.15,12,10),M.skin);hd.position.y=0.8;hd.castShadow=true;torso.add(hd);
 const brim=cyl(0.33,0.33,0.025,M.straw,16);brim.position.y=0.9;torso.add(brim);
 const crown=cyl(0.12,0.15,0.13,M.straw,12);crown.position.y=0.97;torso.add(crown);
 const band=cyl(0.151,0.151,0.03,M.dark,12);band.position.y=0.93;torso.add(band);}
const arms=[];
for(const sx of [-1,1]){const g=new THREE.Group();g.position.set(0.27*sx,0.58,0);const a=cyl(0.055,0.05,0.56,M.white);a.position.y=-0.28;g.add(a);const hand=new THREE.Mesh(new THREE.SphereGeometry(0.05,8,6),M.skin);hand.position.y=-0.58;g.add(hand);torso.add(g);arms.push(g);}
{const st=cyl(0.022,0.026,1.25,M.woodDark,6);st.position.set(0,-0.85,0.06);arms[0].add(st);} // 작대기 in right hand

// 지게
const jige=new THREE.Group();jige.position.set(0,-0.2,-0.27);jige.rotation.x=-0.06;torso.add(jige);
for(const sx of [-1,1]){const p=cyl(0.03,0.04,1.75,M.wood,6);p.position.set(0.19*sx,0.72,0);p.rotation.z=sx*0.035;jige.add(p);
  const pr=new THREE.Group();pr.position.set(0.19*sx,0.28,0);pr.rotation.x=-(Math.PI/2-0.26);const pc=cyl(0.03,0.022,0.5,M.wood,6);pc.position.y=0.25;pr.add(pc);jige.add(pr);}
for(const y of [0.0,0.36,1.05,1.45]){const r=cyl(0.022,0.022,0.39-y*0.035,M.wood,6);r.rotation.z=Math.PI/2;r.position.y=y;jige.add(r);}
{const pad=box(0.3,0.42,0.06,M.straw);pad.position.set(0,0.62,0.07);jige.add(pad);
 for(const sx of [-1,1]){const s=box(0.045,0.62,0.02,M.dark);s.position.set(0.12*sx,0.78,0.16);s.rotation.x=0.25;jige.add(s);}}
const radioPivot=new THREE.Group();radioPivot.position.set(0,0.36,-0.14);jige.add(radioPivot);

function makeRadio(){
  const g=new THREE.Group();
  const body=box(0.56,0.34,0.22,lam(0xc8432b));body.position.y=0.17;g.add(body);
  const trim=lam(0x3a2a22);
  const tt=box(0.58,0.03,0.235,trim);tt.position.y=0.34;g.add(tt);
  const tb=box(0.58,0.03,0.235,trim);tb.position.y=0.015;g.add(tb);
  const panel=box(0.5,0.25,0.012,lam(0xf0e4c8));panel.position.set(0,0.175,-0.112);g.add(panel);
  const grille=new THREE.Mesh(new THREE.CircleGeometry(0.092,20),lam(0x3a302a));grille.position.set(0.11,0.175,-0.119);grille.rotation.y=Math.PI;g.add(grille);
  for(const r of [0.03,0.058,0.084]){const ring=new THREE.Mesh(new THREE.RingGeometry(r,r+0.008,20),lam(0x8a7a62,{side:THREE.DoubleSide}));ring.position.set(0.11,0.175,-0.121);ring.rotation.y=Math.PI;g.add(ring);}
  const dial=new THREE.Mesh(new THREE.PlaneGeometry(0.18,0.07),new THREE.MeshBasicMaterial({color:0xffc35a}));dial.position.set(-0.12,0.22,-0.119);dial.rotation.y=Math.PI;g.add(dial);g.userData.dial=dial;
  const needle=box(0.006,0.06,0.004,new THREE.MeshBasicMaterial({color:0xb3261e}));needle.position.set(-0.1,0.22,-0.122);g.add(needle);
  for(const x of [-0.18,-0.06]){const k=cyl(0.028,0.028,0.03,M.dark,10);k.rotation.x=Math.PI/2;k.position.set(x,0.105,-0.125);g.add(k);}
  const handle=new THREE.Mesh(new THREE.TorusGeometry(0.15,0.016,6,14,Math.PI),trim);handle.position.y=0.35;handle.castShadow=true;g.add(handle);
  const ant=cyl(0.006,0.009,0.55,lam(0xd0d0d0),5);ant.position.set(0.22+0.094,0.35+0.258,0.06);ant.rotation.z=-0.35;g.add(ant);
  return g;
}
const radio=makeRadio();radioPivot.add(radio);
// radioSquash sits at the contact point with no rotation so a bounce can squash the radio in world space
const radioSquash=new THREE.Group();scene.add(radioSquash);
const radioHolder=new THREE.Group();radioHolder.position.y=0.2;radioSquash.add(radioHolder);
const marker=new THREE.Mesh(new THREE.ConeGeometry(0.22,0.45,4),new THREE.MeshBasicMaterial({color:0xffb23e}));marker.rotation.x=Math.PI;marker.visible=false;scene.add(marker);

// ---------------------------------------------------------------- audio
let AC=null,master,musicBus,musicGain,staticGain,muted=false;
const BEAT=60/112;
const MEL=[[64,1],[67,1],[69,1.5],[67,.5],[64,1],[62,1],[60,2],
           [62,1],[64,1],[67,1],[69,.5],[72,.5],[69,1],[67,1],[64,2],
           [69,1],[72,1],[74,1.5],[72,.5],[69,1],[67,1],[69,2],
           [67,1],[64,1],[62,1],[64,.5],[62,.5],[60,4]];
const BARS=[48,43,45,48,41,48,43,48];
let mi=0,bi=0,tNextMel=0,tNextBass=0,tNextTick=0;
function midiF(m){return 440*Math.pow(2,(m-69)/12);}
function radioDetune(){if(R.state!=='carried')return (Math.random()-.5)*70;return clamp(Math.hypot(Math.max(0,B.pitch),B.roll)*45,0,40)*(Math.random()<.5?-1:1);}
function playNote(m,t,dur,type,vol){
  const o=AC.createOscillator(),g=AC.createGain();o.type=type;o.frequency.value=midiF(m);o.detune.value=radioDetune();
  g.gain.setValueAtTime(0.0001,t);g.gain.exponentialRampToValueAtTime(vol,t+0.015);g.gain.exponentialRampToValueAtTime(0.0001,t+dur);
  o.connect(g);g.connect(musicBus);o.start(t);o.stop(t+dur+0.05);
}
let noiseBuf=null;
function playNoise(t,dur,vol,freq,dest){const s=AC.createBufferSource();s.buffer=noiseBuf;const f=AC.createBiquadFilter();f.type='bandpass';f.frequency.value=freq;f.Q.value=1.2;const g=AC.createGain();g.gain.setValueAtTime(vol,t);g.gain.exponentialRampToValueAtTime(0.0001,t+dur);s.connect(f);f.connect(g);g.connect(dest||master);s.start(t,Math.random()*1.5);s.stop(t+dur+0.02);}
function scheduler(){
  if(!AC)return;const ahead=AC.currentTime+0.3;
  while(tNextMel<ahead){const n=MEL[mi];playNote(n[0],tNextMel,n[1]*BEAT*0.92,'triangle',0.2);playNote(n[0]+12,tNextMel,n[1]*BEAT*0.5,'square',0.025);tNextMel+=n[1]*BEAT;mi=(mi+1)%MEL.length;}
  while(tNextBass<ahead){const root=BARS[(bi>>1)%BARS.length],m=(bi&1)?root+7:root;playNote(m,tNextBass,BEAT*1.6,'sine',0.26);tNextBass+=BEAT*2;bi=(bi+1)%(BARS.length*2);}
  while(tNextTick<ahead){playNoise(tNextTick+BEAT*0.5,0.05,0.05,7000,musicBus);tNextTick+=BEAT;}
}
function initAudio(){
  if(AC)return;
  try{AC=new (window.AudioContext||window.webkitAudioContext)();}catch(e){AC=null;return;}
  master=AC.createGain();master.gain.value=0.7;master.connect(AC.destination);
  musicBus=AC.createGain();
  const hp=AC.createBiquadFilter();hp.type='highpass';hp.frequency.value=280;
  const lp=AC.createBiquadFilter();lp.type='lowpass';lp.frequency.value=3200;
  const shaper=AC.createWaveShaper();const cv=new Float32Array(256);for(let i=0;i<256;i++){const x=i/128-1;cv[i]=Math.tanh(x*1.8);}shaper.curve=cv;
  musicGain=AC.createGain();musicGain.gain.value=0.5;
  musicBus.connect(hp);hp.connect(shaper);shaper.connect(lp);lp.connect(musicGain);musicGain.connect(master);
  noiseBuf=AC.createBuffer(1,AC.sampleRate*2,AC.sampleRate);const d=noiseBuf.getChannelData(0);for(let i=0;i<d.length;i++)d[i]=Math.random()*2-1;
  const ns=AC.createBufferSource();ns.buffer=noiseBuf;ns.loop=true;const nf=AC.createBiquadFilter();nf.type='bandpass';nf.frequency.value=2600;nf.Q.value=0.5;
  staticGain=AC.createGain();staticGain.gain.value=0;ns.connect(nf);nf.connect(staticGain);staticGain.connect(master);ns.start();
  tNextMel=tNextBass=tNextTick=AC.currentTime+0.1;
  setInterval(scheduler,60);
}
function playThud(v){if(!AC)return;const t=AC.currentTime;const o=AC.createOscillator(),g=AC.createGain();o.type='sine';o.frequency.setValueAtTime(140,t);o.frequency.exponentialRampToValueAtTime(45,t+0.18);g.gain.setValueAtTime(Math.min(0.6,v*0.12),t);g.gain.exponentialRampToValueAtTime(0.0001,t+0.22);o.connect(g);g.connect(master);o.start(t);o.stop(t+0.25);playNoise(t,0.25,Math.min(0.5,v*0.1),900);}
function playBoing(n){if(!AC)return;const t=AC.currentTime,v=0.34/n;const o=AC.createOscillator(),g=AC.createGain();o.type='sine';
  o.frequency.setValueAtTime(150+n*30,t);o.frequency.exponentialRampToValueAtTime(560+n*70,t+0.11);o.frequency.exponentialRampToValueAtTime(320,t+0.32);
  g.gain.setValueAtTime(0.0001,t);g.gain.exponentialRampToValueAtTime(v,t+0.01);g.gain.exponentialRampToValueAtTime(0.0001,t+0.36);
  o.connect(g);g.connect(master);o.start(t);o.stop(t+0.4);playNoise(t,0.08,v*0.6,1100);}
function playClick(){if(!AC)return;const t=AC.currentTime;playNoise(t,0.05,0.25,3000);playNoise(t+0.08,0.05,0.2,2000);}
function playWin(){if(!AC)return;const t=AC.currentTime+0.05;[72,76,79,84].forEach((m,i)=>{const o=AC.createOscillator(),g=AC.createGain();o.type='triangle';o.frequency.value=midiF(m);g.gain.setValueAtTime(0.0001,t+i*0.13);g.gain.exponentialRampToValueAtTime(0.25,t+i*0.13+0.02);g.gain.exponentialRampToValueAtTime(0.0001,t+i*0.13+0.6);o.connect(g);g.connect(master);o.start(t+i*0.13);o.stop(t+i*0.13+0.7);});}
function setMuted(m){muted=m;$('muteBtn').firstChild.nodeValue=m?'소리 켜기 ':'소리 끄기 ';if(master)master.gain.setTargetAtTime(m?0:0.7,AC.currentTime,0.05);}
$('muteBtn').addEventListener('click',()=>{initAudio();setMuted(!muted);canvas.focus();});

// ---------------------------------------------------------------- game state
const P={x:0,z:0,y:0,yaw:0,yawRate:0,speed:0,accel:0,lean:0,side:0,step:0,busy:0,pathI:0,grace:0};
const B={pitch:0,roll:0,pv:0,rv:0};
const R={state:'carried',pos:new THREE.Vector3(),vel:new THREE.Vector3(),ang:new THREE.Vector3(),q:new THREE.Quaternion(),rest:0,pick:0,from:new THREE.Vector3(),fromQ:new THREE.Quaternion(),bounces:0,air:false,fallT:0,squash:0};
const MAX_BOUNCES=3; // 탱탱볼처럼 최대 3번 튀고, 4번째로 땅에 닿으면 그 자리에서 멈춘다
let game='title',elapsed=0,drops=0,clock=0,titleT=0,toastT=0;
const FALL=0.85,NO_RETURN=0.62,FWD_LIMIT=-0.12;
const keys=new Set();
const camState={orbit:0,dist:7.2,pos:new THREE.Vector3(),look:new THREE.Vector3(),drag:false,lx:0,idle:0};

function reset(){
  const i=8;P.x=PX[i];P.z=PZ[i];P.yaw=Math.atan2(PX[i+4]-PX[i],PZ[i+4]-PZ[i]);P.yawRate=0;P.speed=0;P.accel=0;P.lean=0;P.side=0;P.busy=0;P.pathI=i;
  P.y=groundH(P.x,P.z);
  B.pitch=0;B.roll=0;B.pv=0;B.rv=0;
  attachRadio();elapsed=0;drops=0;$('drops').textContent='0';
  camState.orbit=0;
}
function attachRadio(){radioPivot.add(radio);radio.position.set(0,0,0);radio.rotation.set(0,0,0);R.state='carried';R.squash=0;radioSquash.scale.set(1,1,1);marker.visible=false;}
function syncHolder(){
  radioSquash.position.set(R.pos.x,R.pos.y-0.2,R.pos.z);radioHolder.quaternion.copy(R.q);
  const s=R.squash*R.squash;radioSquash.scale.set(1+0.3*s,1-0.4*s,1+0.3*s);
}

function toast(msg,dur){const t=$('toast');t.textContent=msg;t.classList.add('show');toastT=dur||2.2;}

// input
const GAME_KEYS=new Set(['Space','ArrowUp','ArrowDown','ArrowLeft','ArrowRight']);
addEventListener('keydown',e=>{
  if(GAME_KEYS.has(e.code))e.preventDefault();
  if(e.repeat)return;keys.add(e.code);
  if(e.code==='KeyM'){initAudio();setMuted(!muted);}
  if(e.code==='Space'||e.code==='KeyF')tryPickup();
  if(e.code==='KeyR'&&game==='play'&&e.shiftKey){reset();}
});
addEventListener('keyup',e=>keys.delete(e.code));
addEventListener('blur',()=>keys.clear());
const k=c=>keys.has(c);
canvas.addEventListener('pointerdown',e=>{camState.drag=true;camState.lx=e.clientX;canvas.setPointerCapture(e.pointerId);canvas.focus();});
canvas.addEventListener('pointermove',e=>{if(!camState.drag)return;camState.orbit-= (e.clientX-camState.lx)*0.006;camState.lx=e.clientX;camState.idle=0;});
canvas.addEventListener('pointerup',()=>{camState.drag=false;});
canvas.addEventListener('pointercancel',()=>{camState.drag=false;});
canvas.addEventListener('wheel',e=>{camState.dist=clamp(camState.dist+e.deltaY*0.006,4.5,13);e.preventDefault();},{passive:false});

// touch pad
if(window.matchMedia&&matchMedia('(pointer: coarse)').matches){
  $('touch').hidden=false;$('help').hidden=true;
  document.querySelectorAll('.tbtn').forEach(b=>{const code=b.dataset.key;
    const on=e=>{e.preventDefault();initAudio();keys.add(code);b.classList.add('on');if(code==='Space'||code==='KeyF')tryPickup();};
    const off=e=>{keys.delete(code);b.classList.remove('on');};
    b.addEventListener('pointerdown',on);b.addEventListener('pointerup',off);b.addEventListener('pointercancel',off);b.addEventListener('pointerleave',off);});
}

function startGame(){
  initAudio();if(AC&&AC.state==='suspended')AC.resume();
  reset();game='play';document.body.classList.remove('title');$('titleScreen').hidden=true;$('winScreen').hidden=true;canvas.focus();
  toast('포장길이 끝나면 산길이 시작돼요',2.4);
}
$('startBtn').addEventListener('click',startGame);
$('againBtn').addEventListener('click',startGame);

// ---------------------------------------------------------------- radio physics
const _v=new THREE.Vector3(),_v2=new THREE.Vector3(),_q=new THREE.Quaternion(),_e=new THREE.Euler();
const UP=new THREE.Vector3(0,1,0);
function dropRadio(){
  if(R.state!=='carried')return;
  drops++;$('drops').textContent=drops;
  radio.updateWorldMatrix(true,false);
  const fx=Math.sin(P.yaw),fz=Math.cos(P.yaw),rx=-Math.cos(P.yaw),rz=Math.sin(P.yaw);
  // center of radio in world
  radio.getWorldPosition(R.pos);radio.getWorldQuaternion(R.q);
  _v.set(0,0.17,0).applyQuaternion(R.q);R.pos.add(_v);
  const pb=Math.max(0,B.pitch),dirx=-fx*pb+rx*B.roll,dirz=-fz*pb+rz*B.roll,dl=Math.hypot(dirx,dirz)||1;
  const tdx=dirx/dl,tdz=dirz/dl;
  R.vel.set(fx*P.speed*0.5+tdx*3.0,3.4,fz*P.speed*0.5+tdz*3.0);
  _v.set(tdx,0,tdz);R.ang.crossVectors(UP,_v).multiplyScalar(6.5);
  syncHolder();
  radioHolder.add(radio);radio.position.set(0,-0.17,0);radio.scale.set(1,1,1);radio.rotation.set(0,0,0);
  R.state='falling';R.rest=0;R.bounces=0;R.air=true;R.fallT=0;R.squash=0;marker.visible=true;
  toast(B.pitch>Math.abs(B.roll)?'라디오가 뒤로 떨어졌다!':'라디오가 옆으로 떨어졌다!',2.4);
  B.pitch=0;B.roll=0;B.pv=0;B.rv=0;
}
function updateRadioPhysics(dt){
  const sub=3,h=dt/sub;R.fallT+=dt;
  for(let s=0;s<sub&&R.state==='falling';s++){
    R.vel.y-=9.8*h;R.pos.addScaledVector(R.vel,h);
    const g=groundH(R.pos.x,R.pos.z),rad=0.2;
    if(R.pos.y-rad<g){
      R.pos.y=g+rad;groundN(R.pos.x,R.pos.z,_n);
      const vn=R.vel.dot(_n);
      if(R.air&&vn<0){
        // a new touch of the ground
        R.bounces++;R.air=false;R.squash=1;
        if(R.bounces>MAX_BOUNCES||R.fallT>10){ // 4번째 착지: 그 자리에서 멈춤
          R.vel.set(0,0,0);R.ang.set(0,0,0);R.state='ground';playThud(3);break;
        }
        // 탱탱볼: 매번 확실히 다시 튀어 오르고, 튈수록 조금씩 낮아진다
        const out=Math.max(-vn*0.82,3.6-R.bounces*0.7);
        R.vel.addScaledVector(_n,-vn).multiplyScalar(0.6);
        _v2.copy(_n).lerp(UP,0.6).normalize();R.vel.addScaledVector(_v2,out); // 위쪽으로 튀게 해서 비탈 아래로 멀리 굴러가지 않게
        const hs=Math.hypot(R.vel.x,R.vel.z);if(hs>3.2){R.vel.x*=3.2/hs;R.vel.z*=3.2/hs;}
        R.ang.set(Math.random()-.5,Math.random()-.5,Math.random()-.5).normalize().multiplyScalar(5+Math.random()*5);
        playBoing(R.bounces);
      }else if(vn<0){R.vel.addScaledVector(_n,-vn);}
    }else if(R.pos.y-rad>g+0.04){R.air=true;}
    const w=R.ang.length();if(w>1e-4){_q.setFromAxisAngle(_v.copy(R.ang).multiplyScalar(1/w),w*h);R.q.premultiply(_q);}
  }
  const r=Math.hypot(R.pos.x,R.pos.z);
  if(r>400||R.pos.y<-5){ // lost off the map: put it back next to the player
    R.pos.set(P.x-Math.sin(P.yaw)*1.5,P.y+0.8,P.z-Math.cos(P.yaw)*1.5);R.vel.set(0,0,0);R.air=true;toast('라디오를 가까이에 다시 놓았어요',2);
  }
  syncHolder();
}
function settleRadio(dt){
  // lie on its bottom, facing the same way
  _e.setFromQuaternion(R.q,'YXZ');_q.setFromEuler(_e.set(0,_e.y,0,'YXZ'));
  R.q.slerp(_q,1-Math.exp(-dt*6));
  const g=groundH(R.pos.x,R.pos.z);R.pos.y=lerp(R.pos.y,g+0.17,1-Math.exp(-dt*8));
  syncHolder();
}
function radioDist(){return Math.hypot(R.pos.x-P.x,R.pos.z-P.z);}
function canPickup(){return game==='play'&&R.state==='ground'&&radioDist()<2.4;}
function tryPickup(){
  if(!canPickup())return;
  R.state='pickup';R.pick=0;R.from.copy(R.pos);R.fromQ.copy(R.q);P.busy=0.6;P.speed=0;marker.visible=false;playClick();
}
function updatePickup(dt){
  R.pick+=dt/0.6;const t=Math.min(1,R.pick),e=t*t*(3-2*t);
  radioPivot.updateWorldMatrix(true,false);radioPivot.getWorldPosition(_v);radioPivot.getWorldQuaternion(_q);
  _v2.set(0,0.17,0).applyQuaternion(_q);_v.add(_v2);
  R.pos.lerpVectors(R.from,_v,e);R.pos.y+=Math.sin(e*Math.PI)*0.6;
  R.q.copy(R.fromQ).slerp(_q,e);
  syncHolder();
  if(t>=1){attachRadio();P.grace=1.6;B.pitch=0.05;B.pv=0;B.roll=0;B.rv=0;toast('다시 지게에 얹었다',1.4);}
}

// ---------------------------------------------------------------- update
function update(dt){
  clock+=dt;
  const playing=game==='play';
  if(playing)elapsed+=dt;
  // input
  let fwdIn=((k('KeyW')||k('ArrowUp'))?1:0)-((k('KeyS')||k('ArrowDown'))?1:0);
  let turnIn=((k('KeyA')||k('ArrowLeft'))?1:0)-((k('KeyD')||k('ArrowRight'))?1:0);
  const runT=playing&&(k('ShiftLeft')||k('ShiftRight'));            // 달리기
  const leanT=playing&&R.state==='carried'&&k('Space')?1:0;         // 몸 숙이기
  const sideT=playing?((k('KeyE')?1:0)-(k('KeyQ')?1:0)):0;
  if(!playing||P.busy>0){fwdIn=0;turnIn=0;}
  P.busy=Math.max(0,P.busy-dt);
  P.lean+=(leanT-P.lean)*Math.min(1,dt*7);
  P.side+=(sideT-P.side)*Math.min(1,dt*7);

  const turnMax=lerp(2.0,1.25,clamp(Math.abs(P.speed)/4.4,0,1));
  P.yawRate+=(turnIn*turnMax-P.yawRate)*Math.min(1,dt*5);
  P.yaw+=P.yawRate*dt;
  const fx=Math.sin(P.yaw),fz=Math.cos(P.yaw),rx=-Math.cos(P.yaw),rz=Math.sin(P.yaw);
  const np=nearestPath(P.x,P.z,1);const onTrail=!!(np&&np.d<TRAIL_W);    // 옛 등산로 흔적 위인지
  const hereSlope=slopeAt(P.x,P.z);
  if(np&&np.d<12)P.pathI=np.i;
  const grade=(groundH(P.x+fx*0.6,P.z+fz*0.6)-groundH(P.x-fx*0.6,P.z-fz*0.6))/1.2;
  const sideSlope=(groundH(P.x+rx*0.5,P.z+rz*0.5)-groundH(P.x-rx*0.5,P.z-rz*0.5))/1.0;
  let maxSpd=(runT&&fwdIn>0?6.8:4.4)*(onTrail?1:hereSlope>0.6?0.6:0.82)*(1-P.lean*0.5);
  maxSpd*=clamp(1-Math.max(0,grade)*1.1,0.3,1);
  // too steep to walk straight up: go around, or zig-zag across the slope
  const tooSteep=grade>1.05&&fwdIn>0;          // 절벽(경사 100% 이상)은 못 오른다
  if(tooSteep){maxSpd=0;if(toastT<=0&&playing)toast('너무 가팔라요. 비스듬히 오르거나 다른 길을 찾으세요',2.2);}
  const target=fwdIn>0?maxSpd:fwdIn<0?-1.7:0;
  const prev=P.speed;P.speed+=clamp(target-P.speed,-dt*7,dt*4.5);
  P.accel=lerp(P.accel,(P.speed-prev)/Math.max(dt,1e-3),0.3);
  P.x+=fx*P.speed*dt;P.z+=fz*P.speed*dt;
  // trees and big rocks block the way
  {const bx=Math.floor((P.x+HALF)/BLK),bz=Math.floor((P.z+HALF)/BLK);
   for(let dz=-1;dz<=1;dz++)for(let dx=-1;dx<=1;dx++){const cx=bx+dx,cz=bz+dz;if(cx<0||cz<0||cx>=BLN||cz>=BLN)continue;
     for(const o of blockGrid[cz*BLN+cx]){const ox=P.x-o.x,oz=P.z-o.z,d=Math.hypot(ox,oz),min=o.r+0.32;
       if(d<min&&d>1e-4){P.x=o.x+ox/d*min;P.z=o.z+oz/d*min;P.speed*=0.9;}}}}
  if(grade>1.1&&slopeAt(P.x,P.z)>1.1){P.x-=fx*0.6*dt;P.z-=fz*0.6*dt;} // slide off cliff faces
  const pr=Math.hypot(P.x,P.z);if(pr>395){P.x*=395/pr;P.z*=395/pr;}
  P.y=groundH(P.x,P.z);
  P.step+=Math.abs(P.speed)*dt*2.3;

  // balance
  if(R.state==='carried'&&playing){
    const sp=Math.max(0,P.speed);
    let fp=0,fr=0;
    fp+=P.accel*0.085;
    fp+=grade*sp*0.7;
    fp+=Math.abs(P.yawRate)*sp*0.07;
    fp+=Math.sin(P.step*2)*sp*0.03;
    if(sp>4.8){const rs=(sp-4.4)/2.4;fp+=Math.abs(Math.sin(P.step*2))*0.4*rs;fr+=Math.sin(P.step)*0.3*rs;} // 달리면 라디오가 크게 출렁인다
    if(onTrail&&sp>1&&Math.random()<dt*1.2){B.pv+=Math.random()*0.3*(sp/4.4);B.rv+=(Math.random()-.5)*0.4*(sp/4.4);}
    fp+=fbm(clock*0.9,3.3)*0.3*(sp/4.4);
    fp-=P.lean*1.5;
    fr+=P.yawRate*sp*0.22;
    fr-=sideSlope*(0.35+0.6*Math.min(1,sp/4.4)); // 옆으로 기운 비탈길
    fr+=fbm(clock*0.8,17.1)*0.4*(sp/4.4);
    fr+=P.side*1.05;
    if(!onTrail&&sp>0.5&&Math.random()<dt*1.6){const rough=hereSlope>0.6?1:0.6;B.pv+=(Math.random()*0.8)*rough*(sp/4.4);B.rv+=(Math.random()-.5)*1.1*rough*(sp/4.4);}
    for(const b of bumps){b.cd=Math.max(0,b.cd-dt);if(b.cd>0)continue;const dx=b.x-P.x,dz=b.z-P.z;if(dx*dx+dz*dz<0.55&&sp>0.4){b.cd=1.5;const sev=lerp(0.55,1.05,clamp(P.y/SUMMIT_H,0,1));B.pv+=(0.75+Math.random()*0.5)*sev*(sp/4.4);B.rv+=(Math.random()-.5)*1.4*sev*(sp/4.4);hips.position.y=1.02;}}
    // roots across the trail: harmless at a slow walk, nasty at a run
    for(const rt of roots){rt.cd=Math.max(0,rt.cd-dt);if(rt.cd>0)continue;const dx=P.x-rt.x,dz=P.z-rt.z,al=dx*rt.tx+dz*rt.tz,lat=Math.abs(-dx*rt.tz+dz*rt.tx);
      if(Math.abs(al)<0.3&&lat<rt.half&&sp>0.3){rt.cd=1.2;const imp=0.12+0.03*sp*sp;B.pv+=imp*(0.8+Math.random()*0.4);B.rv+=(Math.random()-.5)*imp;hips.position.y=1.0;}}
    if(P.grace>0){P.grace-=dt;fp*=0.35;fr*=0.35;}
    const KF=3.0,K=9,G=6,C=2.6,SAT=0.45;
    const pa=KF*fp-K*clamp(B.pitch,-SAT,SAT)+G*Math.sin(B.pitch)-C*B.pv;
    const ra=KF*fr-K*clamp(B.roll,-SAT,SAT)+G*Math.sin(B.roll)-C*B.rv;
    B.pv+=pa*dt;B.rv+=ra*dt;B.pitch+=B.pv*dt;B.roll+=B.rv*dt;
    if(B.pitch<FWD_LIMIT){B.pitch=FWD_LIMIT;if(B.pv<0)B.pv*=-0.2;}
    if(B.pitch>FALL||Math.abs(B.roll)>FALL)dropRadio();
  }
  if(R.state==='carried'){radioPivot.rotation.set(-B.pitch,0,B.roll);radio.position.y=Math.abs(Math.sin(P.step*2))*0.012*Math.min(1,Math.abs(P.speed));}
  else if(R.state==='falling'){R.squash=Math.max(0,R.squash-dt*4.5);updateRadioPhysics(dt);}
  else if(R.state==='ground'){R.squash=Math.max(0,R.squash-dt*4.5);settleRadio(dt);}
  else if(R.state==='pickup')updatePickup(dt);

  // win check
  if(playing&&pr<SUMMIT_R){
    if(R.state==='carried')win();
    else if(toastT<=0)toast('라디오를 두고 왔어요! 다시 가져오세요',2.2);
  }

  // rig pose
  player.position.set(P.x,P.y,P.z);player.rotation.y=P.yaw;
  const amp=Math.min(1,Math.abs(P.speed)/3)*(P.speed>4.8?1.45:1);
  legs[0].rotation.x=Math.sin(P.step)*0.6*amp;legs[1].rotation.x=-Math.sin(P.step)*0.6*amp;
  arms[0].rotation.x=-Math.sin(P.step)*0.35*amp-0.15;arms[1].rotation.x=Math.sin(P.step)*0.35*amp-0.5;
  hips.position.y=lerp(hips.position.y,0.92+Math.abs(Math.cos(P.step))*0.05*amp-(P.busy>0?Math.sin(P.busy/0.6*Math.PI)*0.35:0),0.35);
  torso.rotation.x=0.08+P.lean*0.38+(P.busy>0?Math.sin(P.busy/0.6*Math.PI)*0.5:0);
  torso.rotation.z=P.side*0.22;
  {const p=summitFlag.geometry.attributes.position;for(let i=0;i<p.count;i++){const x=p.getX(i);p.setZ(i,Math.sin(clock*4+x*2)*0.28*((x+1.5)/3));}p.needsUpdate=true;}

  if(marker.visible){marker.position.set(R.pos.x,R.pos.y+0.9+Math.sin(clock*4)*0.12,R.pos.z);marker.rotation.y=clock*2;}
  updateCamera(dt);
  sun.position.set(P.x+SUN_OFF.x,P.y+SUN_OFF.y,P.z+SUN_OFF.z);sun.target.position.set(P.x,P.y,P.z);
  if(toastT>0){toastT-=dt;if(toastT<=0)$('toast').classList.remove('show');}
}

function win(){
  game='win';playWin();
  const t=fmt(elapsed);$('wTime').textContent=t;$('wDrops').textContent=drops;
  let best=null;try{best=parseFloat(localStorage.getItem('jige-radio-best'));}catch(e){}
  if(!best||elapsed<best){best=elapsed;try{localStorage.setItem('jige-radio-best',String(elapsed));}catch(e){}}
  $('wBest').textContent=fmt(best);
  $('winMsg').textContent=drops===0?'한 번도 떨어뜨리지 않았어요. 라디오 소리가 산 아래 마을까지 울려 퍼집니다.':drops<=3?'몇 번 넘어졌지만 끝까지 지고 왔어요. 정상에서 듣는 라디오가 각별합니다.':'라디오가 '+drops+'번이나 굴렀지만 아직 잘 나옵니다. 튼튼한 라디오예요.';
  setTimeout(()=>{$('winScreen').hidden=false;},900);
}
function fmt(s){const m=Math.floor(s/60),r=s-m*60;return String(m).padStart(2,'0')+':'+(r<10?'0':'')+r.toFixed(1);}

function updateCamera(dt){
  if(game==='title'){
    titleT+=dt*0.04;const a=titleT+0.6;
    camera.position.set(Math.cos(a)*560,250,Math.sin(a)*560);camera.lookAt(0,70,0);
    camState.pos.copy(camera.position);camState.look.set(0,70,0);return;
  }
  if(!camState.drag){camState.idle+=dt;if(camState.idle>1.2)camState.orbit*=Math.exp(-dt*1.2);}
  let yaw=P.yaw+camState.orbit,dist=camState.dist,ht=3.1+dist*0.12;
  let lookX=P.x,lookY=P.y+1.5,lookZ=P.z;
  if(game==='win'){yaw=P.yaw+clock*0.25;dist=11;ht=4.5;}
  if(R.state==='falling'||R.state==='ground'){const d=radioDist();dist+=Math.min(4,d*0.25);lookX=lerp(P.x,R.pos.x,0.3);lookZ=lerp(P.z,R.pos.z,0.3);}
  const cx=lookX-Math.sin(yaw)*dist,cz=lookZ-Math.cos(yaw)*dist;
  let cy=P.y+ht;cy=Math.max(cy,groundH(cx,cz)+1.2);
  const kk=1-Math.exp(-dt*(game==='play'&&elapsed<1.5?2:4.5));
  camState.pos.lerp(_v.set(cx,cy,cz),kk);camState.look.lerp(_v2.set(lookX,lookY,lookZ),1-Math.exp(-dt*8));
  camera.position.copy(camState.pos);camera.lookAt(camState.look);
  const fov=lerp(camera.fov,game==='play'&&P.speed>4.8?65:58,1-Math.exp(-dt*3));
  if(Math.abs(fov-camera.fov)>0.01){camera.fov=fov;camera.updateProjectionMatrix();}
}

// ---------------------------------------------------------------- HUD
const gc=$('gauge'),gx=gc.getContext('2d');
const lcd=$('lcdText');let lcdMode='';
function drawGauge(){
  const dpr=Math.min(window.devicePixelRatio||1,2),S=gc.clientWidth||124;
  if(gc.width!==Math.round(S*dpr)){gc.width=gc.height=Math.round(S*dpr);}
  gx.setTransform(dpr,0,0,dpr,0,0);gx.clearRect(0,0,S,S);
  const c=S/2,Rr=S/2-4;
  gx.fillStyle='rgba(14,26,22,.8)';gx.beginPath();gx.arc(c,c,Rr,0,Math.PI*2);gx.fill();
  const nr=NO_RETURN/FALL*Rr;
  gx.fillStyle='rgba(228,87,60,.30)';gx.beginPath();gx.arc(c,c,Rr,0,Math.PI*2);gx.arc(c,c,nr,0,Math.PI*2,true);gx.fill();
  // frame side: radio can't fall forward through the 지게
  const fl=c+FWD_LIMIT/FALL*Rr;
  gx.fillStyle='rgba(243,236,220,.12)';gx.fillRect(c-Rr,c-Rr,S,fl-(c-Rr));
  gx.strokeStyle='rgba(243,236,220,.22)';gx.lineWidth=1;
  gx.beginPath();gx.moveTo(c-Rr+6,c);gx.lineTo(c+Rr-6,c);gx.moveTo(c,c-Rr+6);gx.lineTo(c,c+Rr-6);gx.stroke();
  gx.beginPath();gx.arc(c,c,nr,0,Math.PI*2);gx.stroke();
  gx.fillStyle='rgba(243,236,220,.6)';gx.font='600 10px "IBM Plex Sans KR", sans-serif';gx.textAlign='center';gx.textBaseline='middle';
  gx.fillText('지게',c,c-Rr+12);gx.fillText('뒤',c,c+Rr-11);gx.fillText('좌',c-Rr+11,c);gx.fillText('우',c+Rr-11,c);
  let px=c,py=c,col='#ffb23e',danger=false;
  if(R.state==='carried'){px=c+clamp(B.roll/FALL,-1,1)*Rr;py=c+clamp(B.pitch/FALL,-1,1)*Rr;danger=Math.hypot(Math.max(0,B.pitch),B.roll)>NO_RETURN*0.85;if(danger)col='#e4573c';}
  else col='rgba(243,236,220,.25)';
  gx.fillStyle=col;gx.beginPath();gx.arc(px,py,9,0,Math.PI*2);gx.fill();
  gx.strokeStyle='rgba(0,0,0,.35)';gx.lineWidth=2;gx.stroke();
  return danger;
}
const projV=new THREE.Vector3();
const compassEl=$('compass');
function updateHUD(){
  if(game==='title')return;
  const t=clamp(P.y/SUMMIT_H,0,1);
  $('prog').style.width=(t*100).toFixed(1)+'%';
  $('alt').textContent='해발 '+Math.round(ALT0+P.y*ALT_SCALE)+' m · 정상까지 직선 '+Math.round(Math.hypot(P.x,P.z))+' m';
  // compass: arrow points to the summit relative to where the camera looks
  camera.getWorldDirection(projV);
  const rel=Math.atan2(-P.x,-P.z)-Math.atan2(projV.x,projV.z);
  compassEl.style.transform='rotate('+(-rel).toFixed(3)+'rad)';
  $('time').textContent=fmt(elapsed);
  const danger=drawGauge();
  const lbl=$('gaugeLbl');
  let msg='라디오 균형',warn=false;
  if(R.state==='carried'&&game==='play'){
    if(danger){warn=true;msg=B.pitch>Math.abs(B.roll)?'뒤로 넘어가요! Space':(B.roll>0?'오른쪽으로 쏠려요! Q':'왼쪽으로 쏠려요! E');}
  }else if(R.state!=='carried'&&R.state!=='pickup'){msg='라디오를 주우세요';warn=true;}
  if(lbl.textContent!==msg)lbl.textContent=msg;lbl.classList.toggle('warn',warn);
  // radio lcd
  let mode=R.state==='carried'||R.state==='pickup'?(danger?'weak':'ok'):'off';
  if(mode!==lcdMode){lcdMode=mode;lcd.textContent=mode==='ok'?'FM 98.1 ♪ 소리봉 방송':mode==='weak'?'FM 98.1 ~ 지지직…':'-- 신호 약함 --';lcd.classList.toggle('off',mode==='off');}
  // pickup prompt + marker
  $('prompt').hidden=!canPickup();
  const mk=$('marker');
  if(marker.visible&&game==='play'){
    projV.set(R.pos.x,R.pos.y+1.4,R.pos.z).project(camera);
    let sx=(projV.x*0.5+0.5)*innerWidth,sy=(-projV.y*0.5+0.5)*innerHeight;
    if(projV.z>1){sx=innerWidth-sx;sy=innerHeight-40;}
    sx=clamp(sx,60,innerWidth-60);sy=clamp(sy,110,innerHeight-60);
    mk.style.transform='translate('+sx.toFixed(0)+'px,'+sy.toFixed(0)+'px) translate(-50%,-100%)';
    mk.textContent='라디오 '+radioDist().toFixed(0)+' m';mk.hidden=false;
  }else mk.hidden=true;
}
function updateAudio(){
  if(!AC||!musicGain)return;
  const carried=R.state==='carried'||R.state==='pickup';
  const d=carried?0:radioDist();
  const distF=carried?1:Math.max(0.06,1-d/45);
  const tilt=carried&&R.state==='carried'?clamp(Math.hypot(Math.max(0,B.pitch),B.roll)/FALL,0,1):0;
  const stat=carried?tilt*tilt*0.75:0.5;
  const titleDim=game==='title'?0.55:1;
  musicGain.gain.setTargetAtTime(0.5*distF*(1-stat*0.6)*titleDim,AC.currentTime,0.08);
  staticGain.gain.setTargetAtTime(stat*0.2*distF,AC.currentTime,0.06);
}

// ---------------------------------------------------------------- loop
function resize(){renderer.setSize(innerWidth,innerHeight,false);camera.aspect=innerWidth/innerHeight;camera.updateProjectionMatrix();}
addEventListener('resize',resize);
let last=performance.now();
function frame(now){
  const dt=Math.min(0.05,(now-last)/1000);last=now;
  update(dt);updateHUD();updateAudio();
  renderer.render(scene,camera);
  requestAnimationFrame(frame);
}
document.body.classList.add('title');
reset();
requestAnimationFrame(frame);
window.__game={P,B,R,get state(){return game;},keys,dropRadio,PATH_LEN,PX,PZ,PN,PS,tryPickup,groundH,slopeAt,nearestPath,CLIFFS,
  step(n,dt,quiet){for(let i=0;i<n;i++)update(dt);if(!quiet){updateHUD();renderer.render(scene,camera);}},start:startGame};
})();
