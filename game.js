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
const HALF=220, SEG=293, CELL=2*HALF/SEG, VN=SEG+1;
const H=100, SIG=90;
const ALT0=420, ALT_SCALE=(980-420)/H;
const PATH_R0=150, PATH_R1=6, THETA0=Math.PI*0.25;
const PAVE_LEN=110;                       // 초반 포장도로 길이 (m). 이후는 흙 산길
const PAVE_HALF=2.8, TRAIL_HALF=1.55, PATH_BLEND=6;
const SUMMIT_R=7;

function mtnBase(r){return H*Math.exp(-(r*r)/(SIG*SIG));}
function roughAt(x,z){const r=Math.hypot(x,z);return fbm(x/26,z/26)*9*Math.min(1,r/40)+fbm(x/7,z/7)*1.2*Math.min(1,r/20);}
function rawHeight(x,z){
  const r=Math.hypot(x,z);
  let h=mtnBase(r)+roughAt(x,z);
  h=lerp(H,h,smoothstep(8,18,r));
  h*=1-smoothstep(190,215,r);
  return h;
}

// ---------------------------------------------------------------- path
// The trail is "walked" up the mountain: at each step it picks a heading that gives the
// target grade on the slope. Gentle paved road first, then alternating steep pitches (비탈길)
// and short flatter traverses that get steeper toward the summit.
function mtnSlope(r){return H*2*r/(SIG*SIG)*Math.exp(-(r*r)/(SIG*SIG));}
function targetGrade(s){
  if(s<PAVE_LEN)return 0.035;
  const s2=s-PAVE_LEN,prog=clamp(s2/560,0,1),ph=(s2%74)/74;
  const k=smoothstep(0,0.12,ph)*(1-smoothstep(0.45,0.57,ph));
  return lerp(lerp(0.05,0.09,prog),lerp(0.2,0.34,prog),k);
}
function trailWiggle(s){
  if(s<PAVE_LEN)return 0.18*Math.sin(s/30);
  return smoothstep(PAVE_LEN,PAVE_LEN+30,s)*(0.5*Math.sin(s/14)+0.3*Math.sin(s/5.3+1));
}
const _px=[],_pz=[];
{
  let x=PATH_R0*Math.cos(THETA0),z=PATH_R0*Math.sin(THETA0),s=0;const ds=0.35;_px.push(x);_pz.push(z);
  for(let n=0;n<8000;n++){
    const r=Math.hypot(x,z);if(r<PATH_R1)break;
    const ix=-x/r,iz=-z/r,tx=-z/r,tz=x/r;
    const c=clamp(targetGrade(s)/Math.max(mtnSlope(r),1e-6),0,1);
    let a=Math.acos(c)+trailWiggle(s);
    a=Math.max(a,Math.acos(Math.min(1,c*1.3+0.02)));a=Math.min(a,Math.PI/2+0.05);
    x+=(ix*Math.cos(a)+tx*Math.sin(a))*ds;z+=(iz*Math.cos(a)+tz*Math.sin(a))*ds;s+=ds;
    _px.push(x);_pz.push(z);
  }
}
const PN=_px.length;
const PX=Float32Array.from(_px),PZ=Float32Array.from(_pz),PY=new Float32Array(PN),PS=new Float32Array(PN);
const PAVED=new Float32Array(PN),PHALF=new Float32Array(PN);
{
  PS[0]=0;for(let i=1;i<PN;i++){PS[i]=PS[i-1]+Math.hypot(PX[i]-PX[i-1],PZ[i]-PZ[i-1]);}
  const raw=new Float32Array(PN);
  for(let i=0;i<PN;i++){
    PAVED[i]=1-smoothstep(PAVE_LEN-12,PAVE_LEN,PS[i]);
    PHALF[i]=lerp(TRAIL_HALF,PAVE_HALF,PAVED[i]);
    raw[i]=mtnBase(Math.hypot(PX[i],PZ[i]))+0.25*roughAt(PX[i],PZ[i]);
  }
  const W=30;
  for(let i=0;i<PN;i++){let s=0,n=0;for(let k=-W;k<=W;k++){const j=clamp(i+k,0,PN-1);s+=raw[j];n++;}
    PY[i]=s/n+(1-PAVED[i])*fbm(PS[i]/5,7.7)*0.5;} // 산길은 울퉁불퉁
  for(let i=PN-60;i<PN;i++){PY[i]=lerp(PY[i],H,smoothstep(PN-60,PN-1,i));}
}
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

// ---------------------------------------------------------------- heightfield
const HF=new Float32Array(VN*VN), PW=new Float32Array(VN*VN), PV=new Float32Array(VN*VN);
for(let iz=0;iz<VN;iz++)for(let ix=0;ix<VN;ix++){
  const x=-HALF+ix*CELL,z=-HALF+iz*CELL;let h=rawHeight(x,z),pw=0,pv=0;
  const np=nearestPath(x,z,2);
  if(np){
    const hw=PHALF[np.i],w=smoothstep(hw,hw+PATH_BLEND,np.d);
    const tilt=0.16*(1-PAVED[np.i]);           // 산길은 옆으로도 기울어진 비탈길
    const bed=lerp(PY[np.i],h,tilt);
    h=bed*(1-w)+h*w;pw=1-smoothstep(hw-0.4,hw+1.0,np.d);pv=PAVED[np.i];
  }
  HF[iz*VN+ix]=h;PW[iz*VN+ix]=pw;PV[iz*VN+ix]=pv;
}
function groundH(x,z){
  const fx=(x+HALF)/CELL,fz=(z+HALF)/CELL;
  if(fx<0||fz<0||fx>=SEG||fz>=SEG)return 0;
  const ix=Math.floor(fx),iz=Math.floor(fz),tx=fx-ix,tz=fz-iz,i=iz*VN+ix;
  return lerp(lerp(HF[i],HF[i+1],tx),lerp(HF[i+VN],HF[i+VN+1],tx),tz);
}
const _n=new THREE.Vector3();
function groundN(x,z,out){const e=0.4;out.set(groundH(x-e,z)-groundH(x+e,z),2*e,groundH(x,z-e)-groundH(x,z+e)).normalize();return out;}

// ---------------------------------------------------------------- renderer / scene
const canvas=$('game');
const renderer=new THREE.WebGLRenderer({canvas,antialias:true});
renderer.setPixelRatio(Math.min(window.devicePixelRatio||1,1.75));
renderer.setSize(innerWidth,innerHeight,false);
renderer.shadowMap.enabled=true;renderer.shadowMap.type=THREE.PCFSoftShadowMap;
const scene=new THREE.Scene();
const FOG=0xe6d3b0;
scene.background=new THREE.Color(FOG);
scene.fog=new THREE.Fog(FOG,150,950);
const camera=new THREE.PerspectiveCamera(58,innerWidth/innerHeight,0.1,2600);

scene.add(new THREE.HemisphereLight(0xd6e6ff,0x5d4a30,0.72));
const sun=new THREE.DirectionalLight(0xffe7c4,0.9);
sun.castShadow=true;sun.shadow.mapSize.set(2048,2048);
const sc=sun.shadow.camera;sc.left=-34;sc.right=34;sc.top=34;sc.bottom=-34;sc.near=1;sc.far=260;
sun.shadow.bias=-0.0008;
scene.add(sun);scene.add(sun.target);
const SUN_OFF=new THREE.Vector3(-70,95,55);

// sky dome
{
  const g=new THREE.SphereGeometry(1800,32,16),pos=g.attributes.position,cols=[];
  const top=new THREE.Color(0x5f97cf),hor=new THREE.Color(0xf2d6a8),c=new THREE.Color();
  for(let i=0;i<pos.count;i++){const y=pos.getY(i)/1800;c.copy(hor).lerp(top,Math.pow(clamp(y,0,1),0.55));cols.push(c.r,c.g,c.b);}
  g.setAttribute('color',new THREE.Float32BufferAttribute(cols,3));
  const m=new THREE.Mesh(g,new THREE.MeshBasicMaterial({vertexColors:true,side:THREE.BackSide,fog:false,depthWrite:false}));
  scene.add(m);
  const sunDisc=new THREE.Mesh(new THREE.CircleGeometry(60,32),new THREE.MeshBasicMaterial({color:0xfff2d6,fog:false}));
  sunDisc.position.copy(SUN_OFF).normalize().multiplyScalar(1700);sunDisc.lookAt(0,0,0);scene.add(sunDisc);
}

function lam(c,o){return new THREE.MeshLambertMaterial(Object.assign({color:c},o||{}));}

// terrain
{
  const g=new THREE.PlaneGeometry(2*HALF,2*HALF,SEG,SEG);g.rotateX(-Math.PI/2);
  const pos=g.attributes.position,cols=new Float32Array(pos.count*3);
  const cG1=new THREE.Color(0x667f3b),cG2=new THREE.Color(0x9a8a45),cG3=new THREE.Color(0x7d6a3a),cRock=new THREE.Color(0x8a8070),cDirt=new THREE.Color(0xa88655),cGravel=new THREE.Color(0x8f8b80),c=new THREE.Color();
  for(let iz=0;iz<VN;iz++)for(let ix=0;ix<VN;ix++){
    const i=iz*VN+ix,x=-HALF+ix*CELL,z=-HALF+iz*CELL;pos.setY(i,HF[i]);
    const hx=HF[iz*VN+Math.min(ix+1,SEG)]-HF[iz*VN+Math.max(ix-1,0)],hz=HF[Math.min(iz+1,SEG)*VN+ix]-HF[Math.max(iz-1,0)*VN+ix];
    const slope=Math.hypot(hx,hz)/(2*CELL);
    const n1=vnoise(x/14,z/14),n2=vnoise(x/5+40,z/5+40);
    c.copy(cG1).lerp(cG2,n1).lerp(cG3,n2*0.45);
    c.lerp(cRock,smoothstep(0.55,1.1,slope)*0.85);
    c.lerp(cRock,smoothstep(60,82,HF[i])*0.45);
    c.lerp(cDirt,PW[i]*0.9*(1-PV[i]));
    c.lerp(cGravel,PW[i]*0.9*PV[i]);
    cols[i*3]=c.r;cols[i*3+1]=c.g;cols[i*3+2]=c.b;
  }
  g.setAttribute('color',new THREE.BufferAttribute(cols,3));g.computeVertexNormals();
  const terrain=new THREE.Mesh(g,lam(0xffffff,{vertexColors:true}));terrain.receiveShadow=true;scene.add(terrain);
  const ring=new THREE.Mesh(new THREE.RingGeometry(HALF*1.414,3000,64,1),lam(0x6c7a3c));ring.rotation.x=-Math.PI/2;ring.receiveShadow=false;scene.add(ring);
}

// path ribbon
{
  // concrete road (시멘트 포장길) at the start, then a narrow dirt trail with ragged edges
  const pos=[],cols=[],idx=[];
  const cCon=new THREE.Color(0x8d8a82),cJoint=new THREE.Color(0x66635c),cConEdge=new THREE.Color(0x77746c);
  const cDirtA=new THREE.Color(0x9a7c4e),cDirtB=new THREE.Color(0x7f6038),cGrassEdge=new THREE.Color(0x7d7a40);
  const c=new THREE.Color(),ct=new THREE.Color(),cp=new THREE.Color();
  const across=[-1,-0.5,0,0.5,1],NA=across.length;
  const step=2;let row=0;
  for(let i=0;i<PN;i+=step){
    const a=Math.max(0,i-1),b=Math.min(PN-1,i+1);let tx=PX[b]-PX[a],tz=PZ[b]-PZ[a];const tl=Math.hypot(tx,tz)||1;tx/=tl;tz/=tl;
    const nx=-tz,nz=tx,pv=PAVED[i];
    const hw=PHALF[i]*0.94+(1-pv)*0.35*(vnoise(PS[i]/2.2,3.1)-0.5);
    for(let q=0;q<NA;q++){
      const s=across[q]*hw*(1+(1-pv)*0.12*(hash2(i,q)-0.5));
      const x=PX[i]+nx*s,z=PZ[i]+nz*s;pos.push(x,groundH(x,z)+0.09,z);
      const edge=Math.abs(across[q])===1,mid=across[q]===0;
      cp.copy(edge?cConEdge:((PS[i]%5)<0.7?cJoint:cCon));
      ct.copy(edge?cGrassEdge:mid?cDirtB:cDirtA);
      c.copy(ct).lerp(cp,pv).multiplyScalar(0.9+0.2*hash2(i,q*7+3));cols.push(c.r,c.g,c.b);
    }
    if(row>0){for(let q=0;q<NA-1;q++){const o=(row-1)*NA+q,p=row*NA+q;idx.push(o,p,o+1, o+1,p,p+1);}}
    row++;
  }
  const g=new THREE.BufferGeometry();g.setAttribute('position',new THREE.Float32BufferAttribute(pos,3));g.setAttribute('color',new THREE.Float32BufferAttribute(cols,3));g.setIndex(idx);g.computeVertexNormals();
  const m=new THREE.Mesh(g,lam(0xffffff,{vertexColors:true,side:THREE.DoubleSide,polygonOffset:true,polygonOffsetFactor:-2,polygonOffsetUnits:-2}));
  m.receiveShadow=true;scene.add(m);
}

// trees, rocks
const dummy=new THREE.Object3D();
{
  const pines=[],leafy=[],rocks=[];
  for(let k=0;k<5200&&(pines.length+leafy.length)<1500;k++){
    const a=rand()*Math.PI*2,r=14+Math.sqrt(rand())*196;const x=Math.cos(a)*r,z=Math.sin(a)*r;
    const np=nearestPath(x,z,1);if(np&&np.d<6.5)continue;
    const y=groundH(x,z);if(groundN(x,z,_n).y<0.72)continue;
    if(vnoise(x/30+7,z/30+3)<0.28)continue; // clearings
    const s=0.75+rand()*0.75;
    if(y>62&&rand()<0.5)continue;
    (rand()<(y>45?0.75:0.5)?pines:leafy).push({x,y,z,s:s*(y>62?0.7:1),rot:rand()*6.28});
  }
  for(let k=0;k<260;k++){const a=rand()*Math.PI*2,r=10+Math.sqrt(rand())*200,x=Math.cos(a)*r,z=Math.sin(a)*r;const np=nearestPath(x,z,1);if(np&&np.d<3.5)continue;rocks.push({x,y:groundH(x,z),z,s:0.4+rand()*1.3,rot:rand()*6.28});}
  const trunkG=new THREE.CylinderGeometry(0.14,0.22,1,5);trunkG.translate(0,0.5,0);
  const pineLo=new THREE.ConeGeometry(1.5,2.6,7);pineLo.translate(0,2.3,0);
  const pineHi=new THREE.ConeGeometry(1.05,2.1,7);pineHi.translate(0,3.6,0);
  const leafG=new THREE.IcosahedronGeometry(1.55,0);leafG.translate(0,2.6,0);
  const rockG=new THREE.DodecahedronGeometry(0.6,0);
  function inst(geo,mat,list,fn){const m=new THREE.InstancedMesh(geo,mat,list.length);m.castShadow=true;m.receiveShadow=true;const c=new THREE.Color();
    list.forEach((t,i)=>{fn(t,dummy,c);dummy.updateMatrix();m.setMatrixAt(i,dummy.matrix);m.setColorAt(i,c);});m.instanceMatrix.needsUpdate=true;if(m.instanceColor)m.instanceColor.needsUpdate=true;scene.add(m);return m;}
  const all=pines.concat(leafy);
  inst(trunkG,lam(0xffffff),all,(t,d,c)=>{d.position.set(t.x,t.y-0.1,t.z);d.rotation.set(0,t.rot,0);d.scale.set(t.s,t.s*1.9,t.s);c.setHex(0x5e4026);});
  const pinePal=[0x2f5a37,0x3a6a3c,0x2a4d33,0x46703f];
  inst(pineLo,lam(0xffffff,{flatShading:true}),pines,(t,d,c)=>{d.position.set(t.x,t.y,t.z);d.rotation.set(0,t.rot,0);d.scale.setScalar(t.s);c.setHex(pinePal[(t.rot*10|0)%4]);});
  inst(pineHi,lam(0xffffff,{flatShading:true}),pines,(t,d,c)=>{d.position.set(t.x,t.y,t.z);d.rotation.set(0,t.rot,0);d.scale.setScalar(t.s);c.setHex(pinePal[(t.rot*10+1|0)%4]);});
  const autumn=[0xc8452b,0xe07a2e,0xe8b43a,0xb5392a,0xd8962f,0x9a8a3c];
  inst(leafG,lam(0xffffff,{flatShading:true}),leafy,(t,d,c)=>{d.position.set(t.x,t.y,t.z);d.rotation.set(t.rot,t.rot*2,0);d.scale.set(t.s,t.s*1.1,t.s);c.setHex(autumn[(t.rot*13|0)%autumn.length]);});
  inst(rockG,lam(0xffffff,{flatShading:true}),rocks,(t,d,c)=>{d.position.set(t.x,t.y,t.z);d.rotation.set(t.rot,t.rot*1.7,t.rot*.5);d.scale.set(t.s,t.s*0.7,t.s*1.1);c.setRGB(0.52+t.s*0.05,0.5+t.s*0.04,0.46);});
}

// far ridges
{
  const g=new THREE.ConeGeometry(1,1,6);
  const m=new THREE.InstancedMesh(g,lam(0x7f8c98,{flatShading:true}),34);
  for(let i=0;i<34;i++){const a=i/34*Math.PI*2+rand()*0.15,r=520+rand()*260,s=90+rand()*130;dummy.position.set(Math.cos(a)*r,s*0.38-8,Math.sin(a)*r);dummy.rotation.set(0,rand()*3,0);dummy.scale.set(s*1.3,s*0.8,s*1.2);dummy.updateMatrix();m.setMatrixAt(i,dummy.matrix);}
  scene.add(m);
}

// bump stones on the path
const bumps=[];
{
  let i=PS.findIndex(s=>s>PAVE_LEN+8); // 포장도로엔 돌이 없다
  while(i<PN*0.97){
    const t=PS[i]/PATH_LEN;
    const a=Math.max(0,i-1),b=Math.min(PN-1,i+1);let tx=PX[b]-PX[a],tz=PZ[b]-PZ[a];const tl=Math.hypot(tx,tz)||1;
    const off=(rand()*2-1)*1.1;const x=PX[i]-tz/tl*off,z=PZ[i]+tx/tl*off;
    bumps.push({x,z,y:groundH(x,z),s:0.22+rand()*0.16,cd:0});
    i+=Math.floor((lerp(22,8,t)+rand()*9)/0.35);
  }
  const m=new THREE.InstancedMesh(new THREE.DodecahedronGeometry(1,0),lam(0x8c8577,{flatShading:true}),bumps.length);m.castShadow=true;m.receiveShadow=true;
  bumps.forEach((b,k)=>{dummy.position.set(b.x,b.y+0.02,b.z);dummy.rotation.set(k,k*2.3,k*.7);dummy.scale.set(b.s*1.2,b.s*0.6,b.s);dummy.updateMatrix();m.setMatrixAt(k,dummy.matrix);});
  scene.add(m);
}

// tree roots lying across the steep pitches of the trail: you can't step around them
const roots=[];
{
  const rootMat=lam(0x5b3b20);
  let i=PS.findIndex(s=>s>PAVE_LEN+15);
  while(i<PN-40){
    const a=Math.max(0,i-15),b=Math.min(PN-1,i+15),gr=(PY[b]-PY[a])/(PS[b]-PS[a]+1e-6);
    if(gr>0.15){
      let tx=PX[b]-PX[a],tz=PZ[b]-PZ[a];const tl=Math.hypot(tx,tz)||1;tx/=tl;tz/=tl;
      const half=PHALF[i]+0.35,x=PX[i],z=PZ[i];
      const m=new THREE.Mesh(new THREE.CylinderGeometry(0.08,0.12,half*2,6),rootMat);
      m.rotation.set(0,Math.atan2(-tx,-tz),Math.PI/2);m.position.set(x,groundH(x,z)+0.06,z);m.castShadow=true;m.receiveShadow=true;scene.add(m);
      roots.push({x,z,tx,tz,half,cd:0});
      i+=Math.floor((7+rand()*8)/0.35);
    }else i+=Math.floor(3/0.35);
  }
}

// signposts
const signs=[];
function makeSign(l1,l2,at,side){
  const cv=document.createElement('canvas');cv.width=512;cv.height=256;
  const tex=new THREE.CanvasTexture(cv);
  const draw=()=>{const g=cv.getContext('2d');g.fillStyle='#6e4626';g.fillRect(0,0,512,256);
    g.strokeStyle='rgba(0,0,0,.18)';g.lineWidth=3;for(let y=18;y<256;y+=22){g.beginPath();g.moveTo(0,y+Math.sin(y)*4);g.bezierCurveTo(170,y-6,340,y+8,512,y);g.stroke();}
    g.strokeStyle='#4a2d16';g.lineWidth=14;g.strokeRect(7,7,498,242);
    g.fillStyle='#f3ecdc';g.textAlign='center';g.textBaseline='middle';
    g.font='86px "Black Han Sans", "Malgun Gothic", sans-serif';g.fillText(l1,256,104);
    g.font='600 44px "IBM Plex Sans KR", "Malgun Gothic", sans-serif';g.fillStyle='#ffcf7a';g.fillText(l2,256,192);tex.needsUpdate=true;};
  draw();signs.push(draw);
  const grp=new THREE.Group();
  const post=new THREE.Mesh(new THREE.CylinderGeometry(0.07,0.08,2.2,6),lam(0x5a3a20));post.position.y=1.1;post.castShadow=true;grp.add(post);
  const wood=lam(0x6e4626),face=new THREE.MeshLambertMaterial({map:tex});
  const board=new THREE.Mesh(new THREE.BoxGeometry(1.6,0.8,0.08),[wood,wood,wood,wood,face,face]);board.position.y=1.85;board.castShadow=true;grp.add(board);
  const i=clamp(at,1,PN-2);let tx=PX[i+1]-PX[i-1],tz=PZ[i+1]-PZ[i-1];const tl=Math.hypot(tx,tz);tx/=tl;tz/=tl;
  const x=PX[i]-tz*side,z=PZ[i]+tx*side;grp.position.set(x,groundH(x,z),z);
  grp.rotation.y=Math.atan2(tx,tz)+Math.PI;scene.add(grp);
}
function kmLeft(i){return ((PATH_LEN-PS[i])/1000).toFixed(2)+' km';}
makeSign('소리봉 가는 길','정상 '+kmLeft(14),14,4.2);
const iTrail=PS.findIndex(s=>s>PAVE_LEN);makeSign('등산로 입구','포장길 끝 · 정상 '+kmLeft(iTrail),iTrail,3.0);
const iMid=PS.findIndex(s=>s>PATH_LEN*0.5);makeSign('급경사 주의','정상 '+kmLeft(iMid),iMid,3.0);
const iHi=PS.findIndex(s=>s>PATH_LEN*0.8);makeSign('라디오 조심','정상 '+kmLeft(iHi),iHi,-3.0);
if(document.fonts&&document.fonts.ready)document.fonts.ready.then(()=>signs.forEach(f=>f()));

// summit cairn + flag
{
  const g=new THREE.Group();const sm=lam(0x9a9284,{flatShading:true});
  let y=0;for(let k=0;k<7;k++){const s=0.75-k*0.08;const st=new THREE.Mesh(new THREE.DodecahedronGeometry(s,0),sm);st.scale.set(1,0.55,1);st.position.set((rand()-.5)*.15,y+s*0.45,(rand()-.5)*.15);st.rotation.y=k;st.castShadow=true;g.add(st);y+=s*0.8;}
  const pole=new THREE.Mesh(new THREE.CylinderGeometry(0.04,0.04,3.4,6),lam(0x5a3a20));pole.position.set(1.4,1.7,0);pole.castShadow=true;g.add(pole);
  const flag=new THREE.Mesh(new THREE.PlaneGeometry(1.2,0.75,8,1),lam(0xffb23e,{side:THREE.DoubleSide}));flag.position.set(2.0,3.0,0);g.add(flag);g.userData.flag=flag;
  g.position.set(0,groundH(0,0),0);scene.add(g);
  window.__flag=flag;
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
  if(r>206||R.pos.y<-5){ // lost off the map: put it back on the trail
    const i=Math.max(0,P.pathI-10);R.pos.set(PX[i],PY[i]+0.6,PZ[i]);R.vel.set(0,0,0);R.air=true;toast('라디오를 길 위에 다시 놓았어요',2);
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
  const np=nearestPath(P.x,P.z,2);const onPath=!!(np&&np.d<PHALF[np.i]+0.35),onTrail=onPath&&PAVED[np.i]<0.5;
  if(np&&np.d<12)P.pathI=np.i;
  const grade=(groundH(P.x+fx*0.6,P.z+fz*0.6)-groundH(P.x-fx*0.6,P.z-fz*0.6))/1.2;
  const sideSlope=(groundH(P.x+rx*0.5,P.z+rz*0.5)-groundH(P.x-rx*0.5,P.z-rz*0.5))/1.0;
  let maxSpd=(runT&&fwdIn>0?6.8:4.4)*(onPath?1:0.62)*(1-P.lean*0.5);
  maxSpd*=clamp(1-Math.max(0,grade)*1.1,0.45,1);
  const target=fwdIn>0?maxSpd:fwdIn<0?-1.7:0;
  const prev=P.speed;P.speed+=clamp(target-P.speed,-dt*7,dt*4.5);
  P.accel=lerp(P.accel,(P.speed-prev)/Math.max(dt,1e-3),0.3);
  P.x+=fx*P.speed*dt;P.z+=fz*P.speed*dt;
  const pr=Math.hypot(P.x,P.z);if(pr>204){P.x*=204/pr;P.z*=204/pr;}
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
    if(!onPath&&sp>0.5&&Math.random()<dt*2.2){B.pv+=(Math.random()*0.9)*(sp/4.4);B.rv+=(Math.random()-.5)*1.2*(sp/4.4);}
    for(const b of bumps){b.cd=Math.max(0,b.cd-dt);if(b.cd>0)continue;const dx=b.x-P.x,dz=b.z-P.z;if(dx*dx+dz*dz<0.55&&sp>0.4){b.cd=1.5;const sev=lerp(0.55,1.05,PS[P.pathI]/PATH_LEN);B.pv+=(0.75+Math.random()*0.5)*sev*(sp/4.4);B.rv+=(Math.random()-.5)*1.4*sev*(sp/4.4);hips.position.y=1.02;}}
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
  if(window.__flag){const f=window.__flag,p=f.geometry.attributes.position;for(let i=0;i<p.count;i++){const x=p.getX(i);p.setZ(i,Math.sin(clock*5+x*4)*0.08*(x+0.6));}p.needsUpdate=true;}

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
    titleT+=dt*0.05;const a=titleT+0.6;
    camera.position.set(Math.cos(a)*250,120,Math.sin(a)*250);camera.lookAt(0,38,0);
    camState.pos.copy(camera.position);camState.look.set(0,38,0);return;
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
function updateHUD(){
  if(game==='title')return;
  const t=PS[P.pathI]/PATH_LEN;
  $('prog').style.width=(t*100).toFixed(1)+'%';
  $('alt').textContent='해발 '+Math.round(ALT0+P.y*ALT_SCALE)+' m · 정상까지 '+((PATH_LEN-PS[P.pathI])/1000).toFixed(2)+' km';
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
window.__game={P,B,R,get state(){return game;},keys,dropRadio,PATH_LEN,PX,PZ,PN,tryPickup,
  step(n,dt,quiet){for(let i=0;i<n;i++)update(dt);if(!quiet){updateHUD();renderer.render(scene,camera);}},start:startGame};
})();
