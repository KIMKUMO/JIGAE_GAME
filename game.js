(function(){
'use strict';
// Missing elements (e.g. an older cached index.html) must never stop the game loop.
const _dummyEl=document.createElement('div');
const $ = id => document.getElementById(id)||_dummyEl;
function showError(title,detail){
  const box=document.getElementById('errorBox');if(!box)return;
  box.querySelector('b').textContent=title;box.querySelector('span').textContent=detail||'';box.hidden=false;
}
window.addEventListener('error',e=>showError('게임 실행 중 오류가 났어요','새로고침(Ctrl+Shift+R)해 보세요. 계속되면 이 문구를 알려주세요: '+(e.message||'')));
if(!window.THREE){showError('3D 엔진을 불러오지 못했어요','인터넷 연결을 확인하고 새로고침(Ctrl+Shift+R)해 주세요.');return;}

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

// ---------------------------------------------------------------- world layout
// Map (from the sketch): flat foothills along the bottom edge where you start (one of four
// spots, chosen at random), the mountain filling the rest, its summit near the top edge.
// A canyon cuts across the whole mountain: cross it on the swaying rope bridge or wade the ford.
// A creek falls into the canyon as a waterfall, and a cliff band higher up can only be climbed
// at its two gaps. Special patches (구간) are scattered at random on every visit.
const X0=-560,X1=560,Z0=-40,Z1=1300,CELL=2.5;
const SEGX=Math.round((X1-X0)/CELL),SEGZ=Math.round((Z1-Z0)/CELL),VX=SEGX+1,VZ=SEGZ+1;
const MAP={x0:X0+12,x1:X1-12,z0:Z0+12,z1:Z1-12};
const SUMMIT_X=0,SUMMIT_Z=1110,SUMMIT_R=7;
const MTN_Z0=110,H=400;
const START_SLOTS=[-400,-140,140,400],START_Z=35;
let START_X=START_SLOTS[1];
// the layout changes every visit; add ?seed=123 to the address to replay a particular map
const LAYOUT_SEED=(()=>{try{const q=new URLSearchParams(location.search).get('seed');if(q&&isFinite(+q))return (+q)|0;}catch(e){}return (Math.random()*2147483647)|0;})();
const lrand=mulberry32(LAYOUT_SEED);

// an almost straight cone that starts climbing right after the starting meadow, then stepped
// into broad steep belts with narrow benches between them (no long gentle approach any more)
const TERRACE=46,TERRACE_K=2.0;
function terrace(h){const n=Math.floor(h/TERRACE),f=h/TERRACE-n;return (n+0.5+0.5*Math.tanh((f-0.5)*TERRACE_K)/Math.tanh(TERRACE_K/2))*TERRACE;}
function mtnShape(x,z){
  const dz=z<SUMMIT_Z?(SUMMIT_Z-z)/(SUMMIT_Z-MTN_Z0+30):(z-SUMMIT_Z)/170,dx=(x-SUMMIT_X)/640,u=Math.max(0,1-Math.sqrt(dx*dx+dz*dz));
  return terrace(H*u*smoothstep(0,0.07,u));
}
function roughAt(x,z){const foot=lerp(0.35,1,smoothstep(MTN_Z0-60,MTN_Z0+80,z));return (fbm(x/45,z/45)*6+fbm(x/9,z/9)*1.2)*foot;}
function ridgesAt(x,z,m){const f=m/H,amp=8*smoothstep(0.04,0.3,f)*(1-smoothstep(0.75,0.95,f));return (0.35-Math.abs(Math.sin(x/75+fbm(x/120,z/120)*1.5)))*amp;}

// cliff band (절벽): a 16 m wall across the whole mountain, climbable only at two gaps
const CLIFF={z:850+lrand()*60,p:lrand()*6.28,gaps:[]};
{const g1=-430+lrand()*860;let g2;do{g2=-430+lrand()*860;}while(Math.abs(g2-g1)<280);CLIFF.gaps.push({x:g1,hw:26},{x:g2,hw:26});}
function cliffZ(x){return CLIFF.z+22*Math.sin(x/110+CLIFF.p)+9*Math.sin(x/41+CLIFF.p*2);}
function cliffGap(x){let g=0;for(const gp of CLIFF.gaps)g=Math.max(g,1-smoothstep(gp.hw,gp.hw+2.5,Math.abs(x-gp.x)));return g;}   // a clear-cut gap, no half-steep edges
function cliffAdd(x,z){const w=lerp(1.8,32,cliffGap(x)),zc=cliffZ(x);return 16*smoothstep(zc-w,zc+w,z);}

// canyon (계곡) with a river: walls you cannot climb, except the ramps at the ford (여울)
const CAN={z:540+lrand()*80,p1:lrand()*6.28,p2:lrand()*6.28,depth:28,floorHW:5};   // a deep gorge on the steep mountain
function canyonZ(x){return CAN.z+30*Math.sin(x/150+CAN.p1)+11*Math.sin(x/57+CAN.p2);}
// four bridges spread along the canyon: two rope bridges, a single-log bridge and a stone bridge
let FORD_X,BRIDGE_X,FALL_X;const BRIDGE_XS=[],BRIDGE_KIND_LIST=['rope','log','rope','stone'];
{FORD_X=-420+lrand()*840;
 for(let tries=0;tries<500&&BRIDGE_XS.length<BRIDGE_KIND_LIST.length;tries++){const x=-450+lrand()*900;
   if(Math.abs(x-FORD_X)<110||BRIDGE_XS.some(b=>Math.abs(b-x)<150))continue;BRIDGE_XS.push(x);}
 BRIDGE_X=BRIDGE_XS[0];
 for(let tries=0;tries<500;tries++){FALL_X=-430+lrand()*860;if(Math.abs(FALL_X-FORD_X)>=120&&BRIDGE_XS.every(b=>Math.abs(FALL_X-b)>=80))break;}}
function fordW(x){return 1-smoothstep(16,40,Math.abs(x-FORD_X));}
function canyonFloor(x){return mtnShape(x,canyonZ(x))-CAN.depth+fordW(x)*7;}
function canyonCut(x,z,h){
  const d=Math.abs(z-canyonZ(x));if(d>80)return h;
  return Math.min(h,canyonFloor(x)+Math.max(0,d-CAN.floorHW)*lerp(2.4,0.4,fordW(x)));
}
// a creek running down to the canyon, where it drops as a waterfall (폭포)
const CREEK_Z0=canyonZ(FALL_X)+12,CREEK_Z1=Math.min(cliffZ(FALL_X)-30,canyonZ(FALL_X)+250);
function creekX(z){return FALL_X+7*Math.sin(z/38)*smoothstep(CREEK_Z0,CREEK_Z0+35,z);}   // straight where it reaches the lip
function creekCut(x,z,h){if(z<CREEK_Z0||z>CREEK_Z1)return h;const d=Math.abs(x-creekX(z));if(d>6)return h;return h-1.6*(1-smoothstep(1.8,5,d));}

// ---------------------------------------------------------------- special patches (구간)
const Z_STAIRS=0,Z_SCREE=1,Z_STEEP=2,Z_MOSS=3,Z_WIND=4,Z_FOG=5,Z_MUD=6,Z_ROCKFALL=7,Z_LOGS=8,Z_LEAF=9;
const ZONES=[
  {name:'구불구불 돌계단',     desc:'계단은 안전해요. 옆 바위 비탈은 미끄럽고 덜컹거려요'},
  {name:'너덜지대',           desc:'돌이 흘러내려요. 멈춰 있으면 아래로 미끄러져요'},
  {name:'가파른 비탈',         desc:'멈추면 뒤로 밀려 내려가요. Space로 숙이세요'},
  {name:'이끼 낀 바위',        desc:'미끄러워서 잘 멈추지도 돌지도 못해요'},
  {name:'바람 부는 억새 능선', desc:'돌풍이 불면 Q/E로 버티세요'},
  {name:'안개 낀 단풍 숲',     desc:'안개 때문에 앞이 안 보이고 나침반도 꺼져요'},
  {name:'진흙탕',             desc:'발이 푹푹 빠져 아주 느리고 뛸 수 없어요'},
  {name:'낙석 지대',           desc:'위에서 돌이 굴러와요. 맞으면 라디오를 놓쳐요'},
  {name:'쓰러진 나무',         desc:'통나무를 넘을 때마다 덜컹. 천천히 넘으세요'},
  {name:'낙엽 구덩이',         desc:'짙은 자국 밑은 구덩이예요. 빠지면 휘청해요'},
];
const ZONE_COLORS=[0x6e6a60,0x6f695f,0x7c6a52,0x4d6a3c,0xc4ad68,0x6b3d24,0x4a3a28,0x7b736a,0x6a5a34,0xb5652a],ZONE_TINT=[0.8,0.85,0.45,0.75,0.55,0.6,0.8,0.7,0.35,0.75];
const PATCHES=[];
{
  // most of the mountain is special ground now: big patches first, then smaller ones fill the gaps
  const order=[];for(let k=0;k<9;k++)for(let t=0;t<ZONES.length;t++)order.push(t);   // up to 10 kinds x 9 = 90 patches
  for(let i=order.length-1;i>0;i--){const j=Math.floor(lrand()*(i+1));const tmp=order[i];order[i]=order[j];order[j]=tmp;}
  for(let tries=0;tries<45000&&PATCHES.length<order.length;tries++){
    const R=tries<22000?58+lrand()*42:30+lrand()*22,x=-500+lrand()*1000,z=MTN_Z0+35+lrand()*(1060-MTN_Z0-35);
    if(Math.abs(z-canyonZ(x))<R+12||Math.abs(z-cliffZ(x))<R*0.85+6)continue;
    if(Math.hypot(x-SUMMIT_X,z-SUMMIT_Z)<R+28)continue;
    if(BRIDGE_XS.some(bx=>Math.hypot(x-bx,z-canyonZ(bx))<R+30)||Math.hypot(x-FORD_X,z-canyonZ(FORD_X))<R+34)continue;
    if(Math.abs(x-FALL_X)<R+12&&z>CREEK_Z0-20&&z<CREEK_Z1+R)continue;
    if(PATCHES.some(p=>Math.hypot(p.x-x,p.z-z)<(p.R+R)*0.86))continue;   // neighbours may touch a little
    const e=3,gx=(mtnShape(x+e,z)-mtnShape(x-e,z))/(2*e),gz=(mtnShape(x,z+e)-mtnShape(x,z-e))/(2*e),gl=Math.hypot(gx,gz)||1;
    PATCHES.push({x,z,R,type:order[PATCHES.length],ux:gl>1e-6?gx/gl:0,uz:gl>1e-6?gz/gl:1});
  }
}
const _zi={i:-1,w:0,type:-1};
function zoneInfo(x,z,out){
  out.i=-1;out.w=0;out.type=-1;
  for(let i=0;i<PATCHES.length;i++){const p=PATCHES[i],d=Math.hypot(x-p.x,z-p.z);
    if(d<p.R){const w=1-smoothstep(p.R*0.84,p.R,d);if(w>out.w){out.w=w;out.i=i;out.type=p.type;}}}
  return out;
}
function zoneAt(x,z){if(!(isFinite(x)&&isFinite(z))){_zi.i=-1;_zi.w=0;_zi.type=-1;return _zi;}return zoneInfo(x,z,_zi);}

function terrainHeight(x,z){
  const m=mtnShape(x,z),rough=roughAt(x,z);let h=m+ridgesAt(x,z,m);
  const zi=zoneInfo(x,z,_zi);
  if(zi.i>=0){
    const p=PATCHES[zi.i],w=zi.w;
    if(zi.type===Z_STEEP||zi.type===Z_STAIRS||zi.type===Z_ROCKFALL){   // the climb squeezed into a steep pitch
      const lo=mtnShape(p.x-p.ux*p.R,p.z-p.uz*p.R),hi=mtnShape(p.x+p.ux*p.R,p.z+p.uz*p.R);
      if(hi-lo>4){const t=clamp((m-lo)/(hi-lo),0,1),k=zi.type===Z_STEEP?3.6:3.2,tt=0.5+0.5*Math.tanh((t-0.5)*k)/Math.tanh(k/2);h+=(lo+(hi-lo)*tt-m)*w;}
      h+=rough;
      if(zi.type===Z_STAIRS)h+=w*(fbm(x/5.5,z/5.5)*4.2+(vnoise(x/3.4,z/3.4)-0.5)*2.2);   // broken, bouldery slope around the stairs
    }else if(zi.type===Z_SCREE)h+=rough+w*(fbm(x/6,z/6)*3.4+(vnoise(x/4.1,z/4.1)-0.5)*1.6);
    else if(zi.type===Z_MOSS||zi.type===Z_WIND)h+=rough*lerp(1,0.3,w);
    else if(zi.type===Z_MUD)h+=rough*lerp(1,0.2,w)-w*0.6+w*(vnoise(x/5,z/5)-0.5)*0.5;   // soggy hollow
    else h+=rough;
  }else h+=rough;
  h+=cliffAdd(x,z);
  h=canyonCut(x,z,h);h=creekCut(x,z,h);
  const top=mtnShape(SUMMIT_X,SUMMIT_Z)+cliffAdd(SUMMIT_X,SUMMIT_Z);
  return lerp(top,h,smoothstep(8,22,Math.hypot(x-SUMMIT_X,z-SUMMIT_Z)));
}

// ---------------------------------------------------------------- heightfield
const HF=new Float32Array(VX*VZ),ZT=new Int8Array(VX*VZ),ZW=new Float32Array(VX*VZ);
for(let iz=0;iz<VZ;iz++)for(let ix=0;ix<VX;ix++){
  const i=iz*VX+ix;HF[i]=terrainHeight(X0+ix*CELL,Z0+iz*CELL);ZT[i]=_zi.type;ZW[i]=_zi.w;
}
function groundH(x,z){
  const fx=(x-X0)/CELL,fz=(z-Z0)/CELL;
  if(!(fx>=0&&fz>=0&&fx<SEGX&&fz<SEGZ))return 0;
  const ix=Math.floor(fx),iz=Math.floor(fz),tx=fx-ix,tz=fz-iz,i=iz*VX+ix;
  return lerp(lerp(HF[i],HF[i+1],tx),lerp(HF[i+VX],HF[i+VX+1],tx),tz);
}
// generic spatial grid
function makeGrid(cell){const nx=Math.ceil((X1-X0)/cell),nz=Math.ceil((Z1-Z0)/cell);return {cell,nx,nz,cells:Array.from({length:nx*nz},()=>[])};}
function gridAdd(G,x,z,item){G.cells[clamp(Math.floor((z-Z0)/G.cell),0,G.nz-1)*G.nx+clamp(Math.floor((x-X0)/G.cell),0,G.nx-1)].push(item);}
function gridEach(G,x,z,fn){
  if(!(isFinite(x)&&isFinite(z)))return;
  const bx=Math.floor((x-X0)/G.cell),bz=Math.floor((z-Z0)/G.cell);
  for(let dz=-1;dz<=1;dz++)for(let dx=-1;dx<=1;dx++){const cx=bx+dx,cz=bz+dz;if(cx<0||cz<0||cx>=G.nx||cz>=G.nz)continue;
    const L=G.cells[cz*G.nx+cx];for(let k=0;k<L.length;k++)if(fn(L[k])===true)return;}
}

// ---------------------------------------------------------------- winding stone stairs
const TREAD=0.62,STEPS=[],STAIR_STARTS=[];
{
  for(const p of PATCHES){
    if(p.type!==Z_STAIRS)continue;
    const vx=-p.uz,vz=p.ux,span=p.R-6,first=STEPS.length,pts=[];
    for(let k=0;k<=600;k++){const u=k/600,s=lerp(-span,span,u),lat=9*Math.sin(u*Math.PI*3.5)+3*Math.sin(u*Math.PI*9);pts.push([p.x+p.ux*s+vx*lat,p.z+p.uz*s+vz*lat]);}
    let acc=0,next=0;
    for(let k=1;k<pts.length;k++){const [x0,z0]=pts[k-1],[x1,z1]=pts[k],seg=Math.hypot(x1-x0,z1-z0);if(seg<1e-6)continue;
      while(acc+seg>=next){const t=(next-acc)/seg;STEPS.push({x:lerp(x0,x1,t),z:lerp(z0,z1,t),top:0,dx:(x1-x0)/seg,dz:(z1-z0)/seg});next+=TREAD;}acc+=seg;}
    const last=STEPS.length;
    for(let k=first;k<last;k++){let sum=0,n=0;for(let j=Math.max(first,k-4);j<=Math.min(last-1,k+4);j++){sum+=groundH(STEPS[j].x,STEPS[j].z);n++;}STEPS[k].top=sum/n+0.12;}
    for(let k=first+1;k<last;k++)STEPS[k].top=Math.max(STEPS[k].top,STEPS[k-1].top);
    if(last>first)STAIR_STARTS.push(first);
  }
  // carve a bench under the stairs so every step stands ~40 cm proud of the ground. Each ground
  // point takes the height of its NEAREST step (doing it step by step let later, higher steps
  // overwrite earlier ones), and the bench is wide enough that a cross-slope can't bury the edges.
  const near=makeGrid(6);STEPS.forEach((st,k)=>gridAdd(near,st.x,st.z,k));
  const touched=new Set();
  for(const st of STEPS){const ix0=Math.round((st.x-X0)/CELL),iz0=Math.round((st.z-Z0)/CELL);
    for(let iz=iz0-2;iz<=iz0+2;iz++)for(let ix=ix0-2;ix<=ix0+2;ix++)if(ix>=0&&iz>=0&&ix<=SEGX&&iz<=SEGZ)touched.add(iz*VX+ix);}
  for(const i of touched){
    const x=X0+(i%VX)*CELL,z=Z0+((i/VX)|0)*CELL;let bd=1e9;const cand=[];
    gridEach(near,x,z,k=>{const d=Math.hypot(x-STEPS[k].x,z-STEPS[k].z);if(d<5){cand.push([d,STEPS[k].top]);if(d<bd)bd=d;}});
    let bt=1e9;for(const [d,t] of cand)if(d<bd+1.3)bt=Math.min(bt,t);   // the lowest of the closest steps, so no step's edge gets covered
    const w=1-smoothstep(1.9,4.0,bd);if(w>0&&bt<1e8)HF[i]=lerp(HF[i],bt-0.45,w);
  }
}
const stepGrid=makeGrid(6);STEPS.forEach((st,k)=>gridAdd(stepGrid,st.x,st.z,k));
function stepAt(x,z){let best=-1,bd=1e9;
  gridEach(stepGrid,x,z,k=>{const st=STEPS[k],ox=x-st.x,oz=z-st.z,al=Math.abs(ox*st.dx+oz*st.dz),lat=Math.abs(-ox*st.dz+oz*st.dx);
    if(al<TREAD*0.55&&lat<1.25){const d=al+lat*0.1;if(d<bd){bd=d;best=k;}}});
  return best;}

// ---------------------------------------------------------------- swaying rope bridge (흔들다리)
const BRIDGE_KINDS={
  rope: {name:'흔들다리',   desc:'천천히, Q/E로 버티며 건너세요',     toast:'흔들다리 · 뛰면 크게 흔들려요',          half:1.05,rail:0.9, sag:1.8},
  log:  {name:'외나무다리', desc:'가운데로! 떨어지면 계곡 아래예요',  toast:'외나무다리 · A/D로 가운데를 지키세요',    half:0.5, rail:0,   sag:0.4},
  stone:{name:'돌다리',     desc:'흔들리지 않는 튼튼한 다리예요',      toast:'돌다리 · 흔들림 없이 건너요',             half:1.6, rail:1.35,sag:-1.4},
};
// each bridge spans exactly from rim to rim (where the gorge wall meets the slope), plus a little
function rimDist(x,side){const zc=canyonZ(x);for(let d=CAN.floorHW+1;d<70;d+=0.5){const z=zc+side*d;if(slopeAt(x,z)<0.9&&slopeAt(x,z+side)<0.9)return d;}return 30;}
const BRIDGES=BRIDGE_XS.map((x,i)=>{const kind=BRIDGE_KIND_LIST[i],zc=canyonZ(x),b={x,zc,kind,K:BRIDGE_KINDS[kind],z0:zc-rimDist(x,-1)-2.5,z1:zc+rimDist(x,1)+2.5,ang:0,vel:0,bob:0,group:null,pivotY:0};
  b.y0=groundH(x,b.z0)+0.2;b.y1=groundH(x,b.z1)+0.2;b.pivotY=Math.max(b.y0,b.y1)+2.5;return b;});
function bridgeDeck(b,z){const u=clamp((z-b.z0)/(b.z1-b.z0),0,1);return lerp(b.y0,b.y1,u)-b.K.sag*4*u*(1-u)+b.bob*4*u*(1-u);}
// the bridge under (x,z), or null; yHint keeps things down in the canyon from snapping up onto it
// a rope bridge is tied down at both ends and swings in the middle: at swing b.ang the deck's
// centre line moves sideways by up to ~1.4 m mid-span (none at the ends) and the deck tilts.
// These give the swung deck's centre line, tilt and height at (x,z); the planks follow the same.
const ROPE_SWING=5;
function bridgeSpanU(b,z){const u=clamp((z-b.z0)/(b.z1-b.z0),0,1);return 4*u*(1-u);}
function bridgeCenterX(b,z){if(b.kind!=='rope')return b.x;return b.x+ROPE_SWING*Math.sin(b.ang)*bridgeSpanU(b,z);}
function bridgeRoll(b,z){return b.kind==='rope'?b.ang*0.8*bridgeSpanU(b,z):0;}
function deckAt(b,x,z){if(b.kind!=='rope')return bridgeDeck(b,z);return bridgeDeck(b,z)+(x-bridgeCenterX(b,z))*Math.sin(bridgeRoll(b,z));}
function bridgeAt(x,z,y){for(const b of BRIDGES){if(z>b.z0-0.5&&z<b.z1+0.5&&Math.abs(x-bridgeCenterX(b,z))<b.K.half+0.35&&(y===undefined||y>deckAt(b,x,z)-3))return b;}return null;}
function onBridge(x,z,y){return !!bridgeAt(x,z,y);}
// walking surface: ground, a stair step, or the bridge deck (yHint keeps things under the bridge on the ground)
function surfaceH(x,z,yHint){
  const g=groundH(x,z);
  const br=bridgeAt(x,z,yHint);if(br)return Math.max(g,deckAt(br,x,z));
  const k=stepAt(x,z);return k>=0?Math.max(g,STEPS[k].top):g;
}
// only the real barriers count as cliffs: the canyon walls (except the ford) and the cliff band
// (except its gaps). Elsewhere a steep spot just slows you down; it never stops you or throws you off.
function isCliffFeature(x,z){
  if(Math.abs(z-canyonZ(x))<45&&fordW(x)<0.5)return true;
  if(Math.abs(z-cliffZ(x))<8&&cliffGap(x)<0.5)return true;
  return false;
}
function inWater(x,z,y){return Math.abs(z-canyonZ(x))<CAN.floorHW+0.5&&y<canyonFloor(x)+1.2;}

const _n=new THREE.Vector3();
function groundN(x,z,out){const e=0.5;out.set(groundH(x-e,z)-groundH(x+e,z),2*e,groundH(x,z-e)-groundH(x,z+e)).normalize();return out;}
function slopeAt(x,z){const e=0.6;return Math.hypot(groundH(x+e,z)-groundH(x-e,z),groundH(x,z+e)-groundH(x,z-e))/(2*e);}
function downhill(x,z,out){const e=0.8,gx=groundH(x+e,z)-groundH(x-e,z),gz=groundH(x,z+e)-groundH(x,z-e),l=Math.hypot(gx,gz)||1;out.x=-gx/l;out.z=-gz/l;return out;}

// ---------------------------------------------------------------- renderer / scene
const canvas=$('game');
let renderer;
try{renderer=new THREE.WebGLRenderer({canvas,antialias:(window.devicePixelRatio||1)<1.5,powerPreference:'high-performance'});}
catch(err){showError('이 브라우저에서 3D 그래픽(WebGL)을 켤 수 없어요','브라우저 설정에서 "하드웨어 가속 사용"을 켜고 다시 실행해 주세요. Chrome: 설정 → 시스템.');return;}
let pixelRatio=Math.min(window.devicePixelRatio||1,1.5);
renderer.setPixelRatio(pixelRatio);
canvas.addEventListener('webglcontextlost',e=>{e.preventDefault();showError('그래픽이 잠시 멈췄어요','자동으로 복구하는 중이에요. 계속 검은 화면이면 새로고침해 주세요.');},false);
canvas.addEventListener('webglcontextrestored',()=>{const b=document.getElementById('errorBox');if(b)b.hidden=true;},false);
renderer.setSize(innerWidth,innerHeight,false);
renderer.shadowMap.enabled=true;renderer.shadowMap.type=THREE.PCFShadowMap;
const scene=new THREE.Scene();
const FOG=0xe6d3b0,FOG_MIST=0xb8b6ad;
scene.background=new THREE.Color(FOG);
scene.fog=new THREE.Fog(FOG,220,1700);
const camera=new THREE.PerspectiveCamera(58,innerWidth/innerHeight,0.05,3600);

scene.add(new THREE.HemisphereLight(0xd6e6ff,0x5d4a30,0.72));
const sun=new THREE.DirectionalLight(0xffe7c4,0.9);
sun.castShadow=true;sun.shadow.mapSize.set(1024,1024);
const sc=sun.shadow.camera;sc.left=-26;sc.right=26;sc.top=26;sc.bottom=-26;sc.near=1;sc.far=260;
sun.shadow.bias=-0.0008;
scene.add(sun);scene.add(sun.target);
const SUN_OFF=new THREE.Vector3(-70,95,55);

{ // sky dome
  const R0=3000,g=new THREE.SphereGeometry(R0,32,16),pos=g.attributes.position,cols=[];
  const top=new THREE.Color(0x5f97cf),hor=new THREE.Color(0xf2d6a8),c=new THREE.Color();
  for(let i=0;i<pos.count;i++){const y=pos.getY(i)/R0;c.copy(hor).lerp(top,Math.pow(clamp(y,0,1),0.55));cols.push(c.r,c.g,c.b);}
  g.setAttribute('color',new THREE.Float32BufferAttribute(cols,3));
  const sky=new THREE.Mesh(g,new THREE.MeshBasicMaterial({vertexColors:true,side:THREE.BackSide,fog:false,depthWrite:false}));sky.position.set(0,0,600);scene.add(sky);
  const sunDisc=new THREE.Mesh(new THREE.CircleGeometry(90,32),new THREE.MeshBasicMaterial({color:0xfff2d6,fog:false}));
  sunDisc.position.copy(SUN_OFF).normalize().multiplyScalar(2850);sunDisc.position.z+=600;sunDisc.lookAt(0,0,600);scene.add(sunDisc);
}
function lam(c,o){const opts=Object.assign({color:c},o||{});delete opts.flatShading;return new THREE.MeshLambertMaterial(opts);} // r128 Lambert has no flatShading

{ // terrain
  const g=new THREE.PlaneGeometry(X1-X0,Z1-Z0,SEGX,SEGZ);g.rotateX(-Math.PI/2);g.translate((X0+X1)/2,0,(Z0+Z1)/2);
  const pos=g.attributes.position,cols=new Float32Array(pos.count*3);
  const cG1=new THREE.Color(0x667f3b),cG2=new THREE.Color(0x9a8a45),cG3=new THREE.Color(0x7d6a3a),cRock=new THREE.Color(0x8a8070),cCliff=new THREE.Color(0x6f665a),cWet=new THREE.Color(0x5b5a4c),c=new THREE.Color();
  const tints=ZONE_COLORS.map(h=>new THREE.Color(h)),cScree=new THREE.Color(0x9a9286);
  for(let iz=0;iz<VZ;iz++)for(let ix=0;ix<VX;ix++){
    const i=iz*VX+ix,x=X0+ix*CELL,z=Z0+iz*CELL;
    // after rotateX(-90°) PlaneGeometry row iz sits at z=Z0+iz*CELL, so vertex i matches HF[i]
    const vi=i;pos.setY(vi,HF[i]);
    const hx=HF[iz*VX+Math.min(ix+1,SEGX)]-HF[iz*VX+Math.max(ix-1,0)],hz=HF[Math.min(iz+1,SEGZ)*VX+ix]-HF[Math.max(iz-1,0)*VX+ix];
    const slope=Math.hypot(hx,hz)/(2*CELL);
    const n1=vnoise(x/14,z/14),n2=vnoise(x/5+40,z/5+40);
    c.copy(cG1).lerp(cG2,n1).lerp(cG3,n2*0.45);
    if(ZT[i]>=0){c.lerp(tints[ZT[i]],ZW[i]*ZONE_TINT[ZT[i]]*(0.75+0.5*n2));if(ZT[i]===Z_SCREE)c.lerp(cScree,ZW[i]*hash2(ix,iz)*0.55);}
    c.lerp(cRock,smoothstep(0.6,1.0,slope)*0.75);
    c.lerp(cCliff,smoothstep(1.3,2.0,slope));
    if(Math.abs(z-canyonZ(x))<CAN.floorHW+3)c.lerp(cWet,0.6);
    c.lerp(cRock,smoothstep(H*0.75,H*1.05,HF[i])*0.4);
    cols[vi*3]=c.r;cols[vi*3+1]=c.g;cols[vi*3+2]=c.b;
  }
  g.setAttribute('color',new THREE.BufferAttribute(cols,3));g.computeVertexNormals();
  const terrain=new THREE.Mesh(g,lam(0xffffff,{vertexColors:true}));terrain.receiveShadow=true;scene.add(terrain);
  const out=new THREE.Mesh(new THREE.PlaneGeometry(9000,9000),lam(0x6c7a3c));out.rotation.x=-Math.PI/2;out.position.set(0,-3,600);scene.add(out);
}

const dummy=new THREE.Object3D();
function instMesh(geo,mat,list,fn,shadow){const m=new THREE.InstancedMesh(geo,mat,Math.max(1,list.length));m.count=list.length;m.castShadow=shadow!==false;m.receiveShadow=true;const c=new THREE.Color();
  list.forEach((t,i)=>{fn(t,dummy,c);dummy.updateMatrix();m.setMatrixAt(i,dummy.matrix);m.setColorAt(i,c);});m.instanceMatrix.needsUpdate=true;if(m.instanceColor)m.instanceColor.needsUpdate=true;scene.add(m);return m;}

// stone steps
instMesh(new THREE.BoxGeometry(1,1,1),lam(0xffffff),STEPS,(st,d,c)=>{const k=STEPS.indexOf(st);
  let low=st.top;for(const a of [-1.2,0,1.2])for(const b of [-0.35,0.35])low=Math.min(low,groundH(st.x-st.dz*a+st.dx*b,st.z+st.dx*a+st.dz*b));
  const hgt=Math.max(0.95,st.top-low+0.35);   // reach down to the ground so no step floats
  d.position.set(st.x,st.top-hgt/2,st.z);d.rotation.set(0,Math.atan2(st.dx,st.dz)+(hash2(k,3)-0.5)*0.08,0);d.scale.set(2.3+hash2(k,5)*0.3,hgt,TREAD+0.05);const v=0.5+hash2(k,9)*0.12;c.setRGB(v+0.02,v,v-0.04);});

// water: the river on the canyon floor, the creek, and the waterfall
// where the north canyon wall meets the slope above it (the lip the creek spills over)
function northRimZ(x){const zc=canyonZ(x);let z=zc+CAN.floorHW+1;for(;z<zc+60;z+=0.5)if(slopeAt(x,z+0.6)<1.1&&slopeAt(x,z+1.6)<1.1)break;return z;}
const waterMat=new THREE.MeshLambertMaterial({color:0x5a95b8,transparent:true,opacity:0.86});
function ribbon(points,width,mat){ // points: [{x,y,z,tx,tz}]
  const pos=[],idx=[];points.forEach((p,i)=>{const nx=-p.tz,nz=p.tx;pos.push(p.x+nx*width,p.y,p.z+nz*width,p.x-nx*width,p.y,p.z-nz*width);if(i>0){const a=(i-1)*2;idx.push(a,a+2,a+1,a+1,a+2,a+3);}});
  const g=new THREE.BufferGeometry();g.setAttribute('position',new THREE.Float32BufferAttribute(pos,3));g.setIndex(idx);g.computeVertexNormals();
  const m=new THREE.Mesh(g,mat);m.receiveShadow=true;scene.add(m);return m;}
{
  const pts=[];for(let x=X0;x<=X1;x+=4){const z=canyonZ(x),z2=canyonZ(x+1),l=Math.hypot(1,z2-z);pts.push({x,y:canyonFloor(x)+0.45,z,tx:1/l,tz:(z2-z)/l});}
  const river=ribbon(pts,CAN.floorHW-0.4,waterMat);river.material.side=THREE.DoubleSide;
  const cp=[];for(let z=northRimZ(FALL_X)+0.5;z<=CREEK_Z1;z+=3){const x=creekX(z),x2=creekX(z+1),l=Math.hypot(x2-x,1);cp.push({x,y:groundH(x,z)+0.25,z,tx:(x2-x)/l,tz:1/l});}
  ribbon(cp,1.5,waterMat).material.side=THREE.DoubleSide;
  // stepping stones across the ford
  const stones=[];const fz=canyonZ(FORD_X);for(let k=-4;k<=4;k++){const z=fz+k*1.15,x=FORD_X+(hash2(k,7)-0.5)*1.2;stones.push({x,z,y:canyonFloor(FORD_X)+0.5});}
  instMesh(new THREE.CylinderGeometry(0.55,0.65,0.5,7),lam(0x8d877b),stones,(s,d,c)=>{d.position.set(s.x,s.y,s.z);d.rotation.set(0,s.x,0);d.scale.setScalar(1);c.setHex(0x8d877b);});
}
let fallTex=null,fallTex2=null;const WF={};
function softTex(inner,outer){const cv=document.createElement('canvas');cv.width=cv.height=128;const g=cv.getContext('2d');const gr=g.createRadialGradient(64,64,4,64,64,62);gr.addColorStop(0,inner);gr.addColorStop(1,outer);g.fillStyle=gr;g.fillRect(0,0,128,128);return new THREE.CanvasTexture(cv);}
{
  const zc=canyonZ(FALL_X),rimZ=northRimZ(FALL_X),zLip=rimZ+2.5,zBot=zc+CAN.floorHW-0.8,floorY=canyonFloor(FALL_X)+0.45;
  WF.x=FALL_X;WF.zTop=zLip;WF.yTop=groundH(FALL_X,zLip);WF.zBot=zBot;WF.yBot=floorY;
  // streaky falling-water texture (transparent between the streaks so the sheet looks layered)
  const cv=document.createElement('canvas');cv.width=128;cv.height=256;const g=cv.getContext('2d');
  g.fillStyle='rgba(185,222,240,0.55)';g.fillRect(0,0,128,256);
  for(let i=0;i<90;i++){const x=Math.random()*128,w=1+Math.random()*4,y=Math.random()*256,h=30+Math.random()*120,al=0.35+Math.random()*0.6;
    const gr=g.createLinearGradient(0,y,0,y+h);gr.addColorStop(0,'rgba(255,255,255,0)');gr.addColorStop(0.5,'rgba(255,255,255,'+al+')');gr.addColorStop(1,'rgba(255,255,255,0)');g.fillStyle=gr;g.fillRect(x,y,w,h);g.fillRect(x,y-256,w,h);}
  fallTex=new THREE.CanvasTexture(cv);fallTex.wrapS=fallTex.wrapT=THREE.RepeatWrapping;
  fallTex2=fallTex.clone();fallTex2.needsUpdate=true;fallTex2.wrapS=fallTex2.wrapT=THREE.RepeatWrapping;fallTex2.repeat.set(1.6,1);
  // rows from the lip down the rock face to the river; the sheet bows a little away from the wall
  function sheet(lift,widthScale,tex,opacity){
    const N=30,C=6,pos=[],uv=[],idx=[];let acc=0,px=0,py=0,pz=0;
    for(let r=0;r<=N;r++){
      const t=r/N,z=lerp(zLip,zBot,t),bow=Math.sin(Math.PI*Math.min(1,t*1.15))*0.9*(1-t*0.3);
      const half=lerp(1.5,3.4,Math.pow(t,0.8))*widthScale;
      let yc=Math.max(groundH(FALL_X,z),floorY)+lift+bow*0.5;if(r===N)yc=floorY+0.05;
      const zz=z-bow*1.1-lift;
      if(r>0)acc+=Math.hypot(yc-py,zz-pz);px=FALL_X;py=yc;pz=zz;
      for(let c=0;c<=C;c++){const u=c/C,x=FALL_X+(u-0.5)*2*half;pos.push(x,Math.max(yc,groundH(x,z)+lift),zz);uv.push(u,acc/6);}
      if(r>0)for(let c=0;c<C;c++){const a0=(r-1)*(C+1)+c,b0=r*(C+1)+c;idx.push(a0,b0,a0+1,a0+1,b0,b0+1);}
    }
    const geo=new THREE.BufferGeometry();geo.setAttribute('position',new THREE.Float32BufferAttribute(pos,3));geo.setAttribute('uv',new THREE.Float32BufferAttribute(uv,2));geo.setIndex(idx);
    const m=new THREE.Mesh(geo,new THREE.MeshBasicMaterial({map:tex,transparent:true,opacity,side:THREE.DoubleSide,depthWrite:false}));scene.add(m);return m;
  }
  sheet(0.35,1.0,fallTex,0.95);
  sheet(0.75,0.85,fallTex2,0.6);
  // white water where the creek tips over the lip
  const lip=new THREE.Mesh(new THREE.PlaneGeometry(3.4,2.2),new THREE.MeshBasicMaterial({map:softTex('rgba(255,255,255,0.95)','rgba(255,255,255,0)'),transparent:true,depthWrite:false}));
  lip.rotation.x=-Math.PI/2;lip.position.set(FALL_X,WF.yTop+0.35,zLip+0.6);scene.add(lip);
  // foam pool on the river
  const foam=new THREE.Mesh(new THREE.CircleGeometry(5.5,24),new THREE.MeshBasicMaterial({map:softTex('rgba(255,255,255,0.9)','rgba(255,255,255,0)'),transparent:true,depthWrite:false}));
  foam.rotation.x=-Math.PI/2;foam.position.set(FALL_X,floorY+0.08,zBot-1.2);scene.add(foam);WF.foam=foam;
  // soft drifting spray
  const mistTex=softTex('rgba(255,255,255,0.55)','rgba(255,255,255,0)');
  WF.mist=[];for(let k=0;k<8;k++){const sp=new THREE.Sprite(new THREE.SpriteMaterial({map:mistTex,transparent:true,opacity:0.5,depthWrite:false}));
    sp.userData.base=5+hash2(k,4)*4;sp.userData.y=floorY+1.2+hash2(k,6)*2.5;sp.position.set(FALL_X+(hash2(k,2)-0.5)*7,sp.userData.y,zBot-1-hash2(k,1)*3.5);sp.scale.setScalar(sp.userData.base);scene.add(sp);WF.mist.push(sp);}
}

// bridges: rope bridges hang from a pivot above the deck so they can swing sideways
for(const br of BRIDGES){
  const wood=lam(0x8a6038),dark=lam(0x5a3a20);
  if(br.kind==='rope'){
    const g=new THREE.Group(),pivotY=br.pivotY;g.position.set(br.x,pivotY,0);scene.add(g);br.group=g;
    const ropeMat=lam(0x5a4630);
    const part=(m,x,y,z,above)=>{m.position.set(x,y,z);m.userData={bx:x,by:y,z,above};g.add(m);};
    for(let z=br.z0;z<=br.z1;z+=0.55){const p=new THREE.Mesh(new THREE.BoxGeometry(2.1,0.08,0.42),wood);p.castShadow=true;p.receiveShadow=true;part(p,(hash2(z*10|0,1)-0.5)*0.06,bridgeDeck(br,z)-0.04-pivotY,z,-0.04);}
    for(const sx of [-1.05,1.05])for(let z=br.z0;z<br.z1;z+=1.5){const a=bridgeDeck(br,z)+1.0-pivotY,b=bridgeDeck(br,z+1.5)+1.0-pivotY,len=Math.hypot(1.5,b-a);
      const r=new THREE.Mesh(new THREE.CylinderGeometry(0.03,0.03,len,4),ropeMat);r.rotation.x=Math.atan2(1.5,b-a);part(r,sx,(a+b)/2,z+0.75,1.0);
      const v=new THREE.Mesh(new THREE.CylinderGeometry(0.015,0.015,1.0,3),ropeMat);part(v,sx,a-0.5,z,0.5);}
    for(const [z,y] of [[br.z0,br.y0],[br.z1,br.y1]])for(const sx of [-1.2,1.2]){const post=new THREE.Mesh(new THREE.CylinderGeometry(0.12,0.14,2.4,6),dark);post.position.set(br.x+sx,y+1.0,z);post.castShadow=true;scene.add(post);}
  }else if(br.kind==='log'){
    // one fallen trunk across the gap, bark side up, with a few broken branch stubs
    const N=8;for(let k=0;k<N;k++){const za=lerp(br.z0-1.5,br.z1+1.5,k/N),zb=lerp(br.z0-1.5,br.z1+1.5,(k+1)/N),ya=bridgeDeck(br,za)-0.38,yb=bridgeDeck(br,zb)-0.38,len=Math.hypot(zb-za,yb-ya);
      const seg=new THREE.Mesh(new THREE.CylinderGeometry(0.42,0.46,len+0.05,9),lam(0x6b4a2b));seg.position.set(br.x,(ya+yb)/2,(za+zb)/2);seg.rotation.x=Math.atan2(zb-za,yb-ya);seg.castShadow=true;seg.receiveShadow=true;scene.add(seg);}
    for(let k=0;k<5;k++){const z=lerp(br.z0+3,br.z1-3,hash2(k,11)),side=k%2?1:-1,st=new THREE.Mesh(new THREE.CylinderGeometry(0.06,0.09,0.7,5),dark);st.position.set(br.x+side*0.45,bridgeDeck(br,z)-0.2,z);st.rotation.z=side*1.1;scene.add(st);}
    { // the torn-up root plate sits off to one side of the far end, out of the way
      const ball=new THREE.Mesh(new THREE.DodecahedronGeometry(1.0,0),lam(0x5b3f25));ball.position.set(br.x+1.5,br.y1+0.3,br.z1+2.5);ball.scale.set(1,0.8,0.45);ball.castShadow=true;scene.add(ball);}
  }else{
    // arched stone bridge with low parapets and two piers down to the river
    const stone=lam(0x9a948a),stone2=lam(0x86807a);
    for(let z=br.z0-1;z<=br.z1+1;z+=0.85){const y=bridgeDeck(br,z),slab=new THREE.Mesh(new THREE.BoxGeometry(3.3,0.55,0.88),hash2(z*7|0,2)>0.5?stone:stone2);slab.position.set(br.x,y-0.28,z);slab.castShadow=true;slab.receiveShadow=true;scene.add(slab);
      for(const sx of [-1.55,1.55]){const w=new THREE.Mesh(new THREE.BoxGeometry(0.32,0.65,0.86),stone2);w.position.set(br.x+sx,y+0.3,z);w.castShadow=true;scene.add(w);}}
    for(const u of [0.34,0.66]){const z=lerp(br.z0,br.z1,u),top=bridgeDeck(br,z)-0.5,bot=canyonFloor(br.x)-0.5,pier=new THREE.Mesh(new THREE.CylinderGeometry(1.1,1.5,top-bot,8),stone2);pier.position.set(br.x,(top+bot)/2,z);pier.castShadow=true;scene.add(pier);}
  }
}

// trees, rocks, silver grass
const blockG=makeGrid(6),bumpG=makeGrid(6);
function nearBlocker(x,z,gap){let hit=false;gridEach(blockG,x,z,o=>{if(Math.hypot(o.x-x,o.z-z)<o.r+gap){hit=true;return true;}});return hit;}
function nearStairs(x,z,d){let hit=false;gridEach(stepGrid,x,z,k=>{if(Math.hypot(STEPS[k].x-x,STEPS[k].z-z)<d){hit=true;return true;}});return hit;}
function keepClear(x,z){ // places where nothing should grow
  if(Math.abs(z-canyonZ(x))<24)return true;
  if(z>CREEK_Z0-4&&z<CREEK_Z1+2&&Math.abs(x-creekX(z))<5)return true;
  for(const br of BRIDGES)if(Math.abs(x-br.x)<5&&z>br.z0-10&&z<br.z1+10)return true;
  if(z<START_Z+20&&START_SLOTS.some(s=>Math.abs(x-s)<12))return true;
  if(Math.hypot(x-SUMMIT_X,z-SUMMIT_Z)<14)return true;
  return false;
}
{
  const pines=[],leafy=[],rocks=[],grass=[];
  // a tall, tightly packed forest everywhere; special patches keep their own (thinner) cover
  const keep=[0.15,0.12,0.3,0.4,0.06,1.0,0.05,0.1,0.55,0.9];
  for(let k=0;k<260000&&(pines.length+leafy.length)<26000;k++){
    const x=X0+20+rand()*(X1-X0-40),z=Z0+20+rand()*(Z1-Z0-40);
    if(keepClear(x,z))continue;
    const zi=zoneInfo(x,z,_zi),maple=(zi.type===Z_FOG||zi.type===Z_LEAF)&&zi.w>0.3;
    if(rand()>lerp(1,zi.type>=0?keep[zi.type]:1,zi.w))continue;
    if(vnoise(x/40+7,z/40+3)<0.12)continue;                     // only a few small glades
    if(nearStairs(x,z,3.2)||nearBlocker(x,z,2.0))continue;       // trunks ~2.3 m apart: tight, but you can squeeze through
    const y=groundH(x,z);if(slopeAt(x,z)>1.3)continue;
    const tall=lerp(1,0.55,smoothstep(H*0.78,H*0.97,y))*(0.8+rand()*0.45);   // a little shorter up near the summit
    const t={x,y,z,rot:rand()*6.28,g:0.75+rand()*0.5,tall,maple};
    if(maple?rand()<0.1:rand()<lerp(0.5,0.8,smoothstep(0,H*0.7,y)))pines.push(t);else leafy.push(t);
    gridAdd(blockG,x,z,{x,z,r:0.3*t.g+0.06,h:20});
  }
  for(let k=0;k<9000&&rocks.length<2600;k++){const x=X0+20+rand()*(X1-X0-40),z=Z0+20+rand()*(Z1-Z0-40);
    if(keepClear(x,z)||nearStairs(x,z,2.5))continue;
    const zi=zoneInfo(x,z,_zi),scree=(zi.type===Z_SCREE||zi.type===Z_STAIRS)&&zi.w>0.3,moss=zi.type===Z_MOSS&&zi.w>0.3,cliff=slopeAt(x,z)>1.3;
    if(!scree&&!moss&&!cliff&&rand()<0.8)continue;
    const s=0.4+rand()*(scree?1.9:moss?2.2:1.6);if(s>1.3&&nearBlocker(x,z,s*0.6+1.6))continue;
    rocks.push({x,y:groundH(x,z),z,s,rot:rand()*6.28,moss});if(s>1.3)gridAdd(blockG,x,z,{x,z,r:s*0.55,h:s*0.55});}
  // boulder-strewn slope on both sides of every stone staircase: the steps are the safe line
  for(const p of PATCHES){if(p.type!==Z_STAIRS)continue;
    for(let k=0;k<260;k++){const a=rand()*6.283,r=Math.sqrt(rand())*p.R*0.95,x=p.x+Math.cos(a)*r,z=p.z+Math.sin(a)*r;
      if(nearStairs(x,z,2.6))continue;const s=0.6+rand()*1.9;if(s>1.1&&nearBlocker(x,z,s*0.55+0.9))continue;
      rocks.push({x,y:groundH(x,z),z,s,rot:rand()*6.28,moss:false});if(s>1.1)gridAdd(blockG,x,z,{x,z,r:s*0.55,h:s*0.55});}}
  for(let k=0;k<60000&&grass.length<9000;k++){const x=X0+20+rand()*(X1-X0-40),z=MTN_Z0+rand()*(Z1-MTN_Z0-60);
    const zi=zoneInfo(x,z,_zi);if(zi.type!==Z_WIND||rand()>zi.w)continue;
    const n=4+Math.floor(rand()*4),s=0.8+rand()*0.6;
    for(let b=0;b<n;b++){const ang=rand()*6.28;grass.push({x:x+Math.cos(ang)*0.12,y:groundH(x,z),z:z+Math.sin(ang)*0.12,s:s*(0.8+rand()*0.4),rot:ang,lean:0.12+rand()*0.22});}}
  // tall conifers (bare trunk below, a long narrow crown above head height) and tall broadleaf trees
  const trunkG=new THREE.CylinderGeometry(0.62,1,1,6);trunkG.translate(0,0.5,0);
  const coneG=new THREE.ConeGeometry(1,1,7);coneG.translate(0,0.5,0);
  const leafG=new THREE.IcosahedronGeometry(1,0);
  for(const t of pines){t.h=13*t.tall;t.cr=2.3*t.g*Math.sqrt(t.tall);}
  for(const t of leafy){t.h=9*t.tall;t.cr=3.0*t.g*Math.sqrt(t.tall);}
  const all=pines.concat(leafy),barks=[0x5e4026,0x4f3520,0x6a4a2e,0x57412c];
  instMesh(trunkG,lam(0xffffff),all,(t,d,c)=>{d.position.set(t.x,t.y-0.3,t.z);d.rotation.set(0,t.rot,0);d.scale.set(0.3*t.g,t.h+0.3,0.3*t.g);c.setHex(barks[(t.rot*7|0)%4]);});
  const pinePal=[0x2f5a37,0x3a6a3c,0x2a4d33,0x46703f,0x25472f];
  instMesh(coneG,lam(0xffffff),pines,(t,d,c)=>{d.position.set(t.x,t.y+t.h*0.4,t.z);d.rotation.set(0,t.rot,0);d.scale.set(t.cr,t.h*0.48,t.cr);c.setHex(pinePal[(t.rot*10|0)%5]);});
  instMesh(coneG,lam(0xffffff),pines,(t,d,c)=>{d.position.set(t.x,t.y+t.h*0.66,t.z);d.rotation.set(0,t.rot+0.5,0);d.scale.set(t.cr*0.72,t.h*0.48,t.cr*0.72);c.setHex(pinePal[(t.rot*10+1|0)%5]);});
  const autumn=[0xc8452b,0xe07a2e,0xe8b43a,0xb5392a,0xd8962f,0x9a8a3c],maple=[0xd2361f,0xe0521e,0xb8281c,0xe8862a];
  instMesh(leafG,lam(0xffffff),leafy,(t,d,c)=>{d.position.set(t.x,t.y+t.h*0.82+t.cr*0.5,t.z);d.rotation.set(t.rot,t.rot*2,0);d.scale.set(t.cr,t.cr*1.25,t.cr);c.setHex(t.maple?maple[(t.rot*13|0)%4]:autumn[(t.rot*13|0)%autumn.length]);});
  instMesh(new THREE.DodecahedronGeometry(0.6,0),lam(0xffffff),rocks,(t,d,c)=>{d.position.set(t.x,t.y,t.z);d.rotation.set(t.rot,t.rot*1.7,t.rot*.5);d.scale.set(t.s,t.s*(t.moss?0.55:0.7),t.s*1.1);if(t.moss)c.setRGB(0.36,0.46,0.3);else c.setRGB(0.5+Math.min(t.s,2)*0.04,0.48+Math.min(t.s,2)*0.03,0.44);});
  const grassG=new THREE.ConeGeometry(0.05,1.25,3);grassG.translate(0,0.62,0);
  const plumeG=new THREE.ConeGeometry(0.045,0.45,4);plumeG.translate(0,1.42,0);
  const grassPose=(t,d)=>{d.position.set(t.x,t.y-0.05,t.z);d.rotation.set(0,t.rot,0);d.rotateZ(t.lean);d.scale.setScalar(t.s);};
  instMesh(grassG,lam(0xffffff),grass,(t,d,c)=>{grassPose(t,d);c.setRGB(0.72,0.66,0.44);},false);
  instMesh(plumeG,lam(0xffffff),grass,(t,d,c)=>{grassPose(t,d);c.setRGB(0.93,0.9,0.82);},false);
}

{ // far ranges around the map
  const m=new THREE.InstancedMesh(new THREE.ConeGeometry(1,1,6),lam(0x7f8c98),46);
  for(let i=0;i<46;i++){const a=i/46*Math.PI*2+rand()*0.1,r=1300+rand()*500,s=180+rand()*260;dummy.position.set(Math.cos(a)*r,s*0.38-10,600+Math.sin(a)*r);dummy.rotation.set(0,rand()*3,0);dummy.scale.set(s*1.3,s*0.8,s*1.2);dummy.updateMatrix();m.setMatrixAt(i,dummy.matrix);}
  scene.add(m);
}

// small stones: a few everywhere, lots on the scree. Stepping on one jolts the radio.
// fallen logs, leaf litter with hidden holes, mud puddles, and the rockfall boulders
const logG=makeGrid(8),holeG=makeGrid(6),LOGS=[],HOLES=[];
{
  const leaves=[],puddles=[],holeMarks=[];
  for(const p of PATCHES){
    const vx=-p.uz,vz=p.ux;
    if(p.type===Z_LOGS){
      // rows of long fallen trunks across the slope: whichever way you go up, you climb over them
      for(let s=-p.R*0.8;s<=p.R*0.8;s+=4.5+lrand()*2.5){
        const w=Math.sqrt(Math.max(0,p.R*p.R-s*s))*0.95;
        for(let off=-w+lrand()*3;off<w;off+=9+lrand()*3){
          const a=(lrand()-0.5)*0.6,dx=vx*Math.cos(a)-p.ux*Math.sin(a),dz=vz*Math.cos(a)-p.uz*Math.sin(a);
          const L={x:p.x+p.ux*s+vx*off,z:p.z+p.uz*s+vz*off,dx,dz,half:4+lrand()*2.5,hitT:-9};LOGS.push(L);
          for(let sd=-L.half;sd<=L.half;sd+=3)gridAdd(logG,L.x+dx*sd,L.z+dz*sd,L);
        }
      }
    }else if(p.type===Z_LEAF){
      const nh=Math.floor(Math.PI*p.R*p.R/34);
      for(let k=0;k<nh;k++){const a=lrand()*6.283,r=Math.sqrt(lrand())*p.R*0.85,o={x:p.x+Math.cos(a)*r,z:p.z+Math.sin(a)*r,cd:0};HOLES.push(o);gridAdd(holeG,o.x,o.z,o);holeMarks.push(o);}
      for(let k=0;k<2600;k++){const a=lrand()*6.283,r=Math.sqrt(lrand())*p.R,x=p.x+Math.cos(a)*r,z=p.z+Math.sin(a)*r;leaves.push({x,z,y:groundH(x,z)+0.04,rot:lrand()*6.283,c:lrand()});}
    }else if(p.type===Z_MUD){
      for(let k=0;k<70;k++){const a=lrand()*6.283,r=Math.sqrt(lrand())*p.R*0.8,x=p.x+Math.cos(a)*r,z=p.z+Math.sin(a)*r;puddles.push({x,z,y:groundH(x,z)+0.14,s:1+lrand()*2.6,sx:0.6+lrand()*0.8});}
    }
  }
  const logGeo=new THREE.CylinderGeometry(0.22,0.26,1,7);
  instMesh(logGeo,lam(0xffffff),LOGS,(L,d,c)=>{d.position.set(L.x,groundH(L.x,L.z)+0.2,L.z);d.rotation.set(0,Math.atan2(L.dz,-L.dx),Math.PI/2);d.scale.set(1,L.half*2,1);c.setHex(0x6b4a2b);});
  const leafPal=[0xc8452b,0xe07a2e,0xd8962f,0xb5392a,0x9a5a2a];
  const leafGeo=new THREE.PlaneGeometry(0.42,0.32);leafGeo.rotateX(-Math.PI/2);
  instMesh(leafGeo,lam(0xffffff,{side:THREE.DoubleSide}),leaves,(l,d,c)=>{d.position.set(l.x,l.y,l.z);d.rotation.set(0,l.rot,0);d.scale.setScalar(1);c.setHex(leafPal[(l.c*leafPal.length)|0]);},false);
  const discGeo=new THREE.CircleGeometry(1,14);discGeo.rotateX(-Math.PI/2);
  instMesh(discGeo,lam(0xffffff),holeMarks,(o,d,c)=>{d.position.set(o.x,groundH(o.x,o.z)+0.08,o.z);d.rotation.set(0,0,0);d.scale.set(0.75,1,0.75);c.setHex(0x3e1d0c);},false);   // the tell-tale dark patch over a hole
  instMesh(discGeo,new THREE.MeshPhongMaterial({color:0xffffff,shininess:90,specular:0x8a8a8a}),puddles,(o,d,c)=>{d.position.set(o.x,o.y,o.z);d.rotation.set(0,o.s,0);d.scale.set(o.s,1,o.s*o.sx);c.setHex(0x2a2016);},false);   // glossy wet puddles
}
const ROCKS=[],RF={t:2};
{const geo=new THREE.DodecahedronGeometry(0.8,0),mat=lam(0x8a8276);for(let k=0;k<4;k++){const m=new THREE.Mesh(geo,mat);m.castShadow=true;m.visible=false;scene.add(m);ROCKS.push({m,on:false,x:0,z:0,vx:0,vz:0,life:0,hit:false});}}

const bumps=[],roots=[];
{
  for(let k=0;k<60000&&bumps.length<10000;k++){const x=X0+20+rand()*(X1-X0-40),z=Z0+20+rand()*(Z1-Z0-40);
    if(keepClear(x,z)||nearStairs(x,z,1.6))continue;
    const zi=zoneInfo(x,z,_zi),p=zi.type===Z_SCREE?lerp(0.04,1,zi.w):0.04;if(rand()>p)continue;
    const b={x,z,y:groundH(x,z),s:0.22+rand()*0.18,cd:0};bumps.push(b);gridAdd(bumpG,x,z,b);}
  instMesh(new THREE.DodecahedronGeometry(1,0),lam(0x8c8577),bumps,(b,d,c)=>{d.position.set(b.x,b.y+0.02,b.z);d.rotation.set(b.x,b.z,b.s*7);d.scale.set(b.s*1.2,b.s*0.6,b.s);c.setHex(0x8c8577);});
}
function bumpsNear(x,z){const out=[];gridEach(bumpG,x,z,b=>{out.push(b);});return out;}

// signposts
const signs=[];
function makeSign(l1,l2,x,z,faceYaw){
  const cv=document.createElement('canvas');cv.width=256;cv.height=128;   // drawn at half size: there are many signs
  const tex=new THREE.CanvasTexture(cv);
  const fit=(g,text,size,weight,family,maxW)=>{let fs=size;do{g.font=weight+' '+fs+'px '+family;fs-=2;}while(g.measureText(text).width>maxW&&fs>16);};
  const draw=()=>{const g=cv.getContext('2d');g.setTransform(0.5,0,0,0.5,0,0);g.fillStyle='#6e4626';g.fillRect(0,0,512,256);
    g.strokeStyle='rgba(0,0,0,.18)';g.lineWidth=3;for(let y=18;y<256;y+=22){g.beginPath();g.moveTo(0,y+Math.sin(y)*4);g.bezierCurveTo(170,y-6,340,y+8,512,y);g.stroke();}
    g.strokeStyle='#4a2d16';g.lineWidth=14;g.strokeRect(7,7,498,242);
    g.fillStyle='#f3ecdc';g.textAlign='center';g.textBaseline='middle';
    fit(g,l1,80,'','"Black Han Sans", "Malgun Gothic", sans-serif',460);g.fillText(l1,256,100);
    fit(g,l2,36,'600','"IBM Plex Sans KR", "Malgun Gothic", sans-serif',470);g.fillStyle='#ffcf7a';g.fillText(l2,256,190);tex.needsUpdate=true;};
  draw();signs.push(draw);
  const grp=new THREE.Group();
  const post=new THREE.Mesh(new THREE.CylinderGeometry(0.07,0.08,2.2,6),lam(0x5a3a20));post.position.y=1.1;post.castShadow=true;grp.add(post);
  const wood=lam(0x6e4626),face=new THREE.MeshLambertMaterial({map:tex});
  const board=new THREE.Mesh(new THREE.BoxGeometry(1.6,0.8,0.08),[wood,wood,wood,wood,face,face]);board.position.y=1.85;board.castShadow=true;grp.add(board);
  grp.position.set(x,surfaceH(x,z),z);grp.rotation.y=faceYaw;scene.add(grp);
}
for(const sx of START_SLOTS)makeSign('소리봉 정상 '+(Math.hypot(SUMMIT_X-sx,SUMMIT_Z-START_Z)/1000).toFixed(1)+'km','길 없음 · 어디로든 오르세요',sx+2.5,START_Z+5,Math.atan2(0,-1));
for(const p of PATCHES){const x=p.x-p.ux*(p.R+2)+p.uz*3,z=p.z-p.uz*(p.R+2)-p.ux*3;makeSign(ZONES[p.type].name,ZONES[p.type].desc,x,z,Math.atan2(-p.ux,-p.uz));}
for(const br of BRIDGES){makeSign(br.K.name,br.K.desc,br.x+br.K.half+1.6,br.z0-3,Math.atan2(0,-1));makeSign(br.K.name,br.K.desc,br.x-br.K.half-1.6,br.z1+3,Math.atan2(0,1));}
makeSign('여울','물을 건너 계곡을 넘어요',FORD_X+4,canyonZ(FORD_X)-26,Math.atan2(0,-1));
for(const gp of CLIFF.gaps)makeSign('절벽 틈','여기로 오를 수 있어요',gp.x+gp.hw-3,cliffZ(gp.x)-34,Math.atan2(0,-1));
if(document.fonts&&document.fonts.ready)document.fonts.ready.then(()=>signs.forEach(f=>f()));

// summit cairn + a tall flag you can see from far away
let summitFlag=null;
const SUMMIT_H=groundH(SUMMIT_X,SUMMIT_Z);
const ALT0=420, ALT_SCALE=(1350-420)/SUMMIT_H;
{
  const g=new THREE.Group();const sm=lam(0x9a9284);
  let y=0;for(let k=0;k<7;k++){const s=0.75-k*0.08;const st=new THREE.Mesh(new THREE.DodecahedronGeometry(s,0),sm);st.scale.set(1,0.55,1);st.position.set((rand()-.5)*.15,y+s*0.45,(rand()-.5)*.15);st.rotation.y=k;st.castShadow=true;g.add(st);y+=s*0.8;}
  const pole=new THREE.Mesh(new THREE.CylinderGeometry(0.09,0.11,12,6),lam(0x5a3a20));pole.position.set(1.6,6,0);pole.castShadow=true;g.add(pole);
  summitFlag=new THREE.Mesh(new THREE.PlaneGeometry(3,1.8,10,1),new THREE.MeshBasicMaterial({color:0xffb23e,side:THREE.DoubleSide}));
  summitFlag.position.set(3.1,11.0,0);summitFlag.scale.setScalar(1.6);g.add(summitFlag);
  g.position.set(SUMMIT_X,SUMMIT_H,SUMMIT_Z);scene.add(g);
}

// ---------------------------------------------------------------- characters
function box(w,h,d,m){const o=new THREE.Mesh(new THREE.BoxGeometry(w,h,d),m);o.castShadow=true;return o;}
function cyl(rt,rb,h,m,seg){const o=new THREE.Mesh(new THREE.CylinderGeometry(rt,rb,h,seg||8),m);o.castShadow=true;return o;}
const M={skin:lam(0xe2b48c),white:lam(0xece3cc),pants:lam(0x4a586b),wood:lam(0x8b5a2b),woodDark:lam(0x5e3c1e),straw:lam(0xd6b25e),dark:lam(0x2b2520)};

let headMesh=null;
const player=new THREE.Group();scene.add(player);
const hips=new THREE.Group();hips.position.y=0.92;player.add(hips);
const legs=[];
for(const sx of [-1,1]){const g=new THREE.Group();g.position.set(0.11*sx,0,0);const l=cyl(0.075,0.065,0.86,M.pants);l.position.y=-0.43;g.add(l);const f=box(0.12,0.08,0.24,M.dark);f.position.set(0,-0.88,0.05);g.add(f);hips.add(g);legs.push(g);}
const torso=new THREE.Group();hips.add(torso);
{const c=cyl(0.2,0.25,0.64,M.white);c.position.y=0.32;torso.add(c);
 const b=cyl(0.255,0.255,0.07,M.pants);b.position.y=0.04;torso.add(b);
 const hd=new THREE.Mesh(new THREE.SphereGeometry(0.15,12,10),M.skin);hd.position.y=0.8;hd.castShadow=true;torso.add(hd);headMesh=hd;
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
// First person: you see your own arms, 작대기 and legs; only the head is hidden (it still casts a shadow).
const bodyMeshes=[];
player.traverse(o=>{if(o.isMesh){o.material=o.material.clone();bodyMeshes.push(o);}});
const headParts=torso.children.filter(o=>o.isMesh&&o.position.y>=0.75);   // head, hat brim, crown, band
function setBodyVisible(full){for(const m of bodyMeshes){const show=full||!headParts.includes(m);m.material.colorWrite=show;m.material.depthWrite=show;}}
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
  const ws=AC.createBufferSource();ws.buffer=noiseBuf;ws.loop=true;const wl=AC.createBiquadFilter();wl.type='lowpass';wl.frequency.value=900;
  waterGain=AC.createGain();waterGain.gain.value=0;ws.connect(wl);wl.connect(waterGain);waterGain.connect(master);ws.start(0,0.7);
  tNextMel=tNextBass=tNextTick=AC.currentTime+0.1;
  setInterval(scheduler,60);
}
function playThud(v){if(!AC)return;const t=AC.currentTime;const o=AC.createOscillator(),g=AC.createGain();o.type='sine';o.frequency.setValueAtTime(140,t);o.frequency.exponentialRampToValueAtTime(45,t+0.18);g.gain.setValueAtTime(Math.min(0.6,v*0.12),t);g.gain.exponentialRampToValueAtTime(0.0001,t+0.22);o.connect(g);g.connect(master);o.start(t);o.stop(t+0.25);playNoise(t,0.25,Math.min(0.5,v*0.1),900);}
function playBoing(n){if(!AC)return;const t=AC.currentTime,v=0.34/n;const o=AC.createOscillator(),g=AC.createGain();o.type='sine';
  o.frequency.setValueAtTime(150+n*30,t);o.frequency.exponentialRampToValueAtTime(560+n*70,t+0.11);o.frequency.exponentialRampToValueAtTime(320,t+0.32);
  g.gain.setValueAtTime(0.0001,t);g.gain.exponentialRampToValueAtTime(v,t+0.01);g.gain.exponentialRampToValueAtTime(0.0001,t+0.36);
  o.connect(g);g.connect(master);o.start(t);o.stop(t+0.4);playNoise(t,0.08,v*0.6,1100);}
let waterGain=null;
function playGust(){if(!AC)return;const t=AC.currentTime,s=AC.createBufferSource();s.buffer=noiseBuf;const f=AC.createBiquadFilter();f.type='bandpass';f.frequency.setValueAtTime(400,t);f.frequency.linearRampToValueAtTime(900,t+0.8);f.frequency.linearRampToValueAtTime(300,t+2);f.Q.value=0.7;const g=AC.createGain();g.gain.setValueAtTime(0.0001,t);g.gain.exponentialRampToValueAtTime(0.35,t+0.5);g.gain.exponentialRampToValueAtTime(0.0001,t+2.2);s.connect(f);f.connect(g);g.connect(master);s.start(t,Math.random());s.stop(t+2.3);}
function playRumble(){if(!AC)return;const t=AC.currentTime,s=AC.createBufferSource();s.buffer=noiseBuf;const f=AC.createBiquadFilter();f.type='lowpass';f.frequency.value=220;const g=AC.createGain();g.gain.setValueAtTime(0.0001,t);g.gain.exponentialRampToValueAtTime(0.55,t+0.25);g.gain.exponentialRampToValueAtTime(0.0001,t+1.6);s.connect(f);f.connect(g);g.connect(master);s.start(t,Math.random());s.stop(t+1.7);}
function playSquelch(){if(!AC)return;const t=AC.currentTime;playNoise(t,0.12,0.18,320);}
function playCrunch(){if(!AC)return;const t=AC.currentTime;playNoise(t,0.18,0.3,1500);playNoise(t+0.05,0.25,0.25,500);}
function playClick(){if(!AC)return;const t=AC.currentTime;playNoise(t,0.05,0.25,3000);playNoise(t+0.08,0.05,0.2,2000);}
function playWin(){if(!AC)return;const t=AC.currentTime+0.05;[72,76,79,84].forEach((m,i)=>{const o=AC.createOscillator(),g=AC.createGain();o.type='triangle';o.frequency.value=midiF(m);g.gain.setValueAtTime(0.0001,t+i*0.13);g.gain.exponentialRampToValueAtTime(0.25,t+i*0.13+0.02);g.gain.exponentialRampToValueAtTime(0.0001,t+i*0.13+0.6);o.connect(g);g.connect(master);o.start(t+i*0.13);o.stop(t+i*0.13+0.7);});}
function setMuted(m){muted=m;$('muteBtn').firstChild.nodeValue=m?'소리 켜기 ':'소리 끄기 ';if(master)master.gain.setTargetAtTime(m?0:0.7,AC.currentTime,0.05);}
$('muteBtn').addEventListener('click',()=>{initAudio();setMuted(!muted);canvas.focus();});

// ---------------------------------------------------------------- game state
const P={x:0,z:0,y:0,yaw:0,pitch:0,vx:0,vz:0,speed:0,accel:0,lat:0,lean:0,side:0,step:0,busy:0,grace:0,
  yawPrev:0,yawVel:0,yawVelPrev:0,shake:0,stair:-1,zone:-1,wasBridge:false,wasWet:false,mudStep:0,deckVel:0,deckAcc:0};
const B={pitch:0,roll:0,pv:0,rv:0};
const R={state:'carried',pos:new THREE.Vector3(),vel:new THREE.Vector3(),ang:new THREE.Vector3(),q:new THREE.Quaternion(),rest:0,pick:0,from:new THREE.Vector3(),fromQ:new THREE.Quaternion(),bounces:0,air:false,fallT:0,squash:0};
// 떨어질 때마다 1~3번 중 무작위로 튀고, 그다음 땅에 닿으면 그 자리에서 멈춘다
let game='title',elapsed=0,drops=0,clock=0,titleT=0,toastT=0;
const FALL=0.85,NO_RETURN=0.62,FWD_LIMIT=-0.12;
const keys=new Set();
const camState={pos:new THREE.Vector3(),look:new THREE.Vector3(),drag:false,lx:0,ly:0};

function reset(){
  START_X=START_SLOTS[Math.floor(Math.random()*START_SLOTS.length)]+(Math.random()-0.5)*16;   // 출발 위치는 네 곳 중 무작위
  P.x=START_X;P.z=START_Z;P.yaw=Math.atan2(SUMMIT_X-START_X,SUMMIT_Z-START_Z);P.pitch=0.05;P.vx=0;P.vz=0;P.speed=0;P.accel=0;P.lat=0;P.lean=0;P.side=0;P.busy=0;
  P.yawPrev=P.yaw;P.yawVel=0;P.yawVelPrev=0;P.shake=0;P.stair=-1;P.zone=-1;
  P.y=surfaceH(P.x,P.z);
  B.pitch=0;B.roll=0;B.pv=0;B.rv=0;
  attachRadio();elapsed=0;drops=0;$('drops').textContent='0';
  if(typeof evEnd==='function'&&EV){evEnd();EV.t=28;EV.last=-1;}
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
// mouse look: click the view to lock the mouse (Esc releases it). Where pointer lock is not
// available (touch, some embedded frames) dragging the view does the same.
const LOOK_SENS=0.0022;
let locked=false;
const isTouch=!!(window.matchMedia&&matchMedia('(pointer: coarse)').matches);
function look(dx,dy){if(!isFinite(dx)||!isFinite(dy))return;dx=clamp(dx,-300,300);dy=clamp(dy,-300,300);P.yaw-=dx*LOOK_SENS;P.pitch=clamp(P.pitch-dy*LOOK_SENS,-1.35,1.25);}
function requestLook(){
  if(game!=='play'||isTouch||!canvas.requestPointerLock)return;
  try{const pr=canvas.requestPointerLock();if(pr&&pr.catch)pr.catch(()=>{});}catch(e){}
}
function updateLookHint(){$('lookHint').hidden=locked||game!=='play'||isTouch;}
document.addEventListener('pointerlockchange',()=>{locked=document.pointerLockElement===canvas;updateLookHint();});
addEventListener('mousemove',e=>{if(locked)look(e.movementX||0,e.movementY||0);});
canvas.addEventListener('pointerdown',e=>{canvas.focus();if(e.pointerType==='mouse'&&!locked)requestLook();camState.drag=true;camState.lx=e.clientX;camState.ly=e.clientY;try{canvas.setPointerCapture(e.pointerId);}catch(_){}});
canvas.addEventListener('pointermove',e=>{if(!camState.drag||locked)return;look((e.clientX-camState.lx)*1.4,(e.clientY-camState.ly)*1.4);camState.lx=e.clientX;camState.ly=e.clientY;});
canvas.addEventListener('pointerup',()=>{camState.drag=false;});
canvas.addEventListener('pointercancel',()=>{camState.drag=false;});

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
  setBodyVisible(false);requestLook();updateLookHint();
  toast('길은 없어요. 어느 쪽으로든 정상까지 올라가세요',2.6);
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
  R.vel.set(P.vx*0.5+tdx*3.0,4.2,P.vz*0.5+tdz*3.0);
  _v.set(tdx,0,tdz);R.ang.crossVectors(UP,_v).multiplyScalar(6.5);
  syncHolder();
  radioHolder.add(radio);radio.position.set(0,-0.17,0);radio.scale.set(1,1,1);radio.rotation.set(0,0,0);
  R.state='falling';R.rest=0;R.bounces=0;R.maxB=1+Math.floor(Math.random()*3);R.air=true;R.fallT=0;R.squash=0;marker.visible=true;
  toast(B.pitch>Math.abs(B.roll)?'라디오가 뒤로 떨어졌다!':'라디오가 옆으로 떨어졌다!',2.4);
  B.pitch=0;B.roll=0;B.pv=0;B.rv=0;
}
function updateRadioPhysics(dt){
  const sub=3,h=dt/sub;R.fallT+=dt;
  for(let s=0;s<sub&&R.state==='falling';s++){
    R.vel.y-=9.8*h;R.pos.addScaledVector(R.vel,h);
    // trunks and boulders: bounce off them
    gridEach(blockG,R.pos.x,R.pos.z,o=>{const ox=R.pos.x-o.x,oz=R.pos.z-o.z,d=Math.hypot(ox,oz),min=o.r+0.24;
      if(d<min&&d>1e-4&&R.pos.y<groundH(o.x,o.z)+(o.h||2)){const nx=ox/d,nz=oz/d;R.pos.x=o.x+nx*min;R.pos.z=o.z+nz*min;
        const vn=R.vel.x*nx+R.vel.z*nz;if(vn<0){R.vel.x-=1.55*vn*nx;R.vel.z-=1.55*vn*nz;R.ang.set(Math.random()-.5,Math.random()-.5,Math.random()-.5).normalize().multiplyScalar(6);if(-vn>1)playThud(-vn*0.8);}}});
    const g=surfaceH(R.pos.x,R.pos.z,R.pos.y),rad=0.2;
    if(R.pos.y-rad<g){
      R.pos.y=g+rad;groundN(R.pos.x,R.pos.z,_n);
      const vn=R.vel.dot(_n);
      if(R.air&&vn<0){
        // a new touch of the ground
        R.bounces++;R.air=false;R.squash=1;
        if(R.bounces>R.maxB||R.fallT>10){ // 정해진 횟수(1~3번)만큼 튄 뒤 다음 착지에서 그 자리에 멈춤
          R.vel.set(0,0,0);R.ang.set(0,0,0);R.state='ground';playThud(3);break;
        }
        // 탱탱볼: 매번 확실히 다시 튀어 오르고, 튈수록 조금씩 낮아진다
        const out=clamp(-vn*0.9,6.6-R.bounces*1.2,7);   // 약 1.5m → 0.9m → 0.45m, 아무리 세게 떨어져도 2.5m까지만
        // 높은 곳에서 떨어져 세게 부딪힐수록 옆으로도 멀리 튀어 나간다
        // 지게 높이에서 떨어지면 한 번에 2m쯤, 10m 위에서 떨어지면 6m쯤 날아가고 이후 튕김에도 일부 이어진다
        const impact=-vn;
        let hx=R.vel.x-_n.x*vn,hz=R.vel.z-_n.z*vn;let hl=Math.hypot(hx,hz);
        if(hl<0.3){hx=_n.x;hz=_n.z;hl=Math.hypot(hx,hz);if(hl<0.05){const a=Math.random()*Math.PI*2;hx=Math.cos(a);hz=Math.sin(a);hl=1;}} // 거의 수직이면 비탈 아래쪽으로
        const fly=Math.min(6,Math.max(0.3*impact,0.55*hl));
        _v2.copy(_n).lerp(UP,0.6).normalize();
        R.vel.set(hx/hl*fly,0,hz/hl*fly).addScaledVector(_v2,out);
        R.ang.set(Math.random()-.5,Math.random()-.5,Math.random()-.5).normalize().multiplyScalar(5+Math.random()*5);
        playBoing(R.bounces);
      }else if(vn<0){R.vel.addScaledVector(_n,-vn);}
    }else if(R.pos.y-rad>g+0.04){R.air=true;}
    const w=R.ang.length();if(w>1e-4){_q.setFromAxisAngle(_v.copy(R.ang).multiplyScalar(1/w),w*h);R.q.premultiply(_q);}
  }
  const lost=R.pos.x<MAP.x0||R.pos.x>MAP.x1||R.pos.z<MAP.z0||R.pos.z>MAP.z1||R.pos.y<groundH(R.pos.x,R.pos.z)-6;
  // down in the gorge (on the river floor) while you're up top: carry it back to the nearest bridge
  const inGorge=Math.abs(R.pos.z-canyonZ(R.pos.x))<CAN.floorHW+2&&R.pos.y<canyonFloor(R.pos.x)+3&&P.y>canyonFloor(P.x)+6;
  if(inGorge&&!lost){
    let best=null,bd=1e9;for(const b of BRIDGES){const d=Math.abs(b.x-R.pos.x);if(d<bd){bd=d;best=b;}}
    if(best){const near=P.z<best.zc,zz=near?best.z0-2.5:best.z1+2.5,xx=best.x+(near?1:-1)*0.8;
      R.pos.set(xx,groundH(xx,zz)+0.9,zz);R.vel.set(0,0,0);R.ang.set(0,0,0);R.air=true;R.bounces=R.maxB;   // just drops down and settles
      toast('협곡에 떨어진 라디오가 '+best.K.name+' 초입으로 돌아왔어요',2.6);syncHolder();return;}
  }
  const sunk=inWater(R.pos.x,R.pos.z,R.pos.y)&&!inWater(P.x,P.z,P.y);
  if(lost||sunk){ // off the map, or into the river while you're up on the bank: put it back next to you
    R.pos.set(P.x-Math.sin(P.yaw)*1.5,P.y+0.8,P.z-Math.cos(P.yaw)*1.5);R.vel.set(0,0,0);R.air=true;
    toast(sunk?'강물에 빠진 라디오를 건져 왔어요':'라디오를 가까이에 다시 놓았어요',2);
  }
  syncHolder();
}
function settleRadio(dt){
  // lie on its bottom, facing the same way
  _e.setFromQuaternion(R.q,'YXZ');_q.setFromEuler(_e.set(0,_e.y,0,'YXZ'));
  R.q.slerp(_q,1-Math.exp(-dt*6));
  const g=surfaceH(R.pos.x,R.pos.z,R.pos.y);R.pos.y=lerp(R.pos.y,g+0.17,1-Math.exp(-dt*8));
  syncHolder();
}
function radioDist(){return Math.hypot(R.pos.x-P.x,R.pos.z-P.z);}
function canPickup(){return game==='play'&&R.state==='ground'&&radioDist()<2.4;}
function tryPickup(){
  if(!canPickup())return;
  R.state='pickup';R.pick=0;R.from.copy(R.pos);R.fromQ.copy(R.q);P.busy=0.6;P.vx=0;P.vz=0;P.speed=0;marker.visible=false;playClick();
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
// gusts on the windy ridges
const WIND={t:2+Math.random()*3,on:0,dur:0,dir:0,str:0,x:0,z:0};
const _dh={x:0,z:0};
let fogMix=0;
// ---------------------------------------------------------------- one-off hazards
// Every so often, while you carry the radio, one thing happens once: a magpie dives at the radio,
// a boar charges, a wasp swarm gives chase, a branch snaps overhead, or a snake lies in your way.
// Each is announced (sound, message and direction arrow) a moment before it strikes, each can be
// dodged, and when it is over it is gone: nothing keeps bothering you.
const EV={t:28,cur:null,last:-1,n:0,buzz:null};
const EV_NAMES={magpie:'까치',boar:'멧돼지',wasps:'말벌 떼',branch:'부러진 가지',snake:'뱀'};
const EV_KINDS=Object.keys(EV_NAMES);
const evRoot=new THREE.Group();scene.add(evRoot);
const evM={};
{
  // magpie (drawn a bit larger than life so it reads at a distance)
  const g=new THREE.Group(),black=lam(0x16181d),white=lam(0xecebe4),blue=lam(0x2a4470);
  const body=new THREE.Mesh(new THREE.SphereGeometry(0.18,8,6),black);body.scale.set(1,0.9,1.7);g.add(body);
  const belly=new THREE.Mesh(new THREE.SphereGeometry(0.15,8,6),white);belly.scale.set(1.05,0.8,1.2);belly.position.set(0,-0.05,0);g.add(belly);
  const head=new THREE.Mesh(new THREE.SphereGeometry(0.11,8,6),black);head.position.set(0,0.08,0.3);g.add(head);
  const beak=new THREE.Mesh(new THREE.ConeGeometry(0.035,0.13,5),black);beak.rotation.x=Math.PI/2;beak.position.set(0,0.07,0.44);g.add(beak);
  const tail=new THREE.Mesh(new THREE.BoxGeometry(0.1,0.02,0.55),blue);tail.position.set(0,0.03,-0.5);g.add(tail);
  const wg1=new THREE.BoxGeometry(0.6,0.02,0.26);wg1.translate(0.3,0,0);const wg2=wg1.clone();wg2.translate(-0.6,0,0);
  const wl=new THREE.Mesh(wg1,black),wr=new THREE.Mesh(wg2,black);g.add(wl,wr);
  const tip1=new THREE.Mesh(new THREE.BoxGeometry(0.22,0.025,0.2),white);tip1.position.set(0.42,0,0);wl.add(tip1);
  const tip2=tip1.clone();tip2.position.set(-0.42,0,0);wr.add(tip2);
  g.scale.setScalar(1.7);g.visible=false;evRoot.add(g);evM.magpie={g,wl,wr};
}
{
  // boar
  const g=new THREE.Group(),fur=lam(0x3f3226),dark=lam(0x241b14),tusk=lam(0xf1ead8),snout=lam(0x6b4a3a);
  const body=new THREE.Mesh(new THREE.BoxGeometry(0.72,0.72,1.45),fur);body.position.y=0.78;g.add(body);
  const ridge=new THREE.Mesh(new THREE.BoxGeometry(0.2,0.16,1.2),dark);ridge.position.set(0,1.18,0.05);g.add(ridge);
  const head=new THREE.Group();head.position.set(0,0.78,0.78);g.add(head);
  const skull=new THREE.Mesh(new THREE.BoxGeometry(0.52,0.5,0.55),fur);skull.position.set(0,0,0.2);head.add(skull);
  const nose=new THREE.Mesh(new THREE.CylinderGeometry(0.13,0.15,0.3,8),snout);nose.rotation.x=Math.PI/2;nose.position.set(0,-0.1,0.58);head.add(nose);
  for(const s of [-1,1]){const t=new THREE.Mesh(new THREE.ConeGeometry(0.035,0.2,5),tusk);t.position.set(s*0.15,-0.12,0.6);t.rotation.set(-0.6,0,s*0.5);head.add(t);
    const e=new THREE.Mesh(new THREE.ConeGeometry(0.08,0.2,4),dark);e.position.set(s*0.2,0.3,0.05);head.add(e);}
  const legs=[];for(const [lx,lz] of [[-0.24,0.5],[0.24,0.5],[-0.24,-0.5],[0.24,-0.5]]){const p=new THREE.Group();p.position.set(lx,0.5,lz);const l=new THREE.Mesh(new THREE.BoxGeometry(0.16,0.5,0.16),dark);l.position.y=-0.25;p.add(l);g.add(p);legs.push(p);}
  g.traverse(o=>{if(o.isMesh)o.castShadow=true;});g.scale.setScalar(1.15);g.visible=false;evRoot.add(g);evM.boar={g,head,legs};
}
{
  // wasp swarm: a cloud of little striped bodies
  const g=new THREE.Group(),y=lam(0xf0b81e),k=lam(0x1a1408),geo=new THREE.SphereGeometry(0.05,5,4);geo.scale(1,1,1.8);
  const bees=[];for(let i=0;i<22;i++){const m=new THREE.Mesh(geo,i%3?y:k);g.add(m);bees.push({m,a:Math.random()*6.3,b:Math.random()*6.3,r:0.3+Math.random()*0.6,s:3+Math.random()*4});}
  g.visible=false;evRoot.add(g);evM.wasps={g,bees};
}
{
  // a heavy branch with leaves, and its shadow on the ground
  const g=new THREE.Group(),bark=lam(0x4d3826),leaf=lam(0x6f7d34);
  const main=new THREE.Mesh(new THREE.CylinderGeometry(0.1,0.17,4.2,7),bark);main.rotation.z=Math.PI/2;g.add(main);
  for(const [x,a,l] of [[-1.1,0.7,1.4],[0.3,-0.8,1.6],[1.3,0.6,1.1]]){const t=new THREE.Mesh(new THREE.CylinderGeometry(0.04,0.07,l,5),bark);t.position.set(x,0,0);t.rotation.set(0,a,Math.PI/2-0.9);t.translateY(l/2);g.add(t);
    const c=new THREE.Mesh(new THREE.IcosahedronGeometry(0.55,0),leaf);c.position.copy(t.position).add(new THREE.Vector3(Math.cos(a)*0.2,0.5,-Math.sin(a)*l*0.5));g.add(c);}
  g.traverse(o=>{if(o.isMesh)o.castShadow=true;});
  const sg=new THREE.CircleGeometry(1,24);sg.rotateX(-Math.PI/2);
  const shadow=new THREE.Mesh(sg,new THREE.MeshBasicMaterial({color:0x000000,transparent:true,opacity:0,depthWrite:false}));shadow.renderOrder=2;
  g.visible=false;shadow.visible=false;evRoot.add(g,shadow);evM.branch={g,shadow};
}
{
  // snake: a chain of beads that slithers
  const g=new THREE.Group(),c1=lam(0x2e2618),c2=lam(0xc29a2a),segs=[];
  for(let i=0;i<24;i++){const r=i===0?0.1:0.088*(1-i/30);const m=new THREE.Mesh(new THREE.SphereGeometry(r,7,5),i%3===1?c2:c1);m.scale.set(1,0.7,1.5);g.add(m);segs.push(m);}
  const eye=lam(0xd8c21a);for(const s of [-1,1]){const e=new THREE.Mesh(new THREE.SphereGeometry(0.018,5,4),eye);e.position.set(s*0.05,0.04,0.04);segs[0].add(e);}
  g.visible=false;evRoot.add(g);evM.snake={g,segs};
}

// sounds
function evOsc(type,f0,f1,t,dur,vol,filt){const o=AC.createOscillator(),g=AC.createGain(),f=AC.createBiquadFilter();o.type=type;o.frequency.setValueAtTime(f0,t);o.frequency.exponentialRampToValueAtTime(f1,t+dur);
  f.type='bandpass';f.frequency.value=filt;f.Q.value=1.4;g.gain.setValueAtTime(0.0001,t);g.gain.exponentialRampToValueAtTime(vol,t+0.02);g.gain.exponentialRampToValueAtTime(0.0001,t+dur);o.connect(f);f.connect(g);g.connect(master);o.start(t);o.stop(t+dur+0.05);}
function playCaw(){if(!AC)return;const t=AC.currentTime;for(let i=0;i<3;i++){evOsc('sawtooth',1250,780,t+i*0.2,0.15,0.22,1500);}}
function playGrunt(){if(!AC)return;const t=AC.currentTime;evOsc('sawtooth',95,62,t,0.35,0.45,320);evOsc('sawtooth',90,58,t+0.42,0.3,0.4,300);playNoise(t,0.3,0.22,260);}
function playHiss(){if(!AC)return;const t=AC.currentTime;playNoise(t,1.0,0.32,5200);playNoise(t+0.1,0.9,0.22,7500);}
function playCrack(){if(!AC)return;const t=AC.currentTime;for(let i=0;i<6;i++)playNoise(t+i*0.06+Math.random()*0.03,0.05,0.55,2200+Math.random()*1500);playNoise(t+0.38,0.35,0.4,700);}
function startBuzz(){if(!AC||EV.buzz)return;const g=AC.createGain(),f=AC.createBiquadFilter();f.type='bandpass';f.frequency.value=650;f.Q.value=2;g.gain.value=0;
  const o1=AC.createOscillator(),o2=AC.createOscillator(),lfo=AC.createOscillator(),lg=AC.createGain();o1.type='sawtooth';o2.type='sawtooth';o1.frequency.value=212;o2.frequency.value=227;lfo.frequency.value=23;lg.gain.value=18;
  lfo.connect(lg);lg.connect(o1.frequency);lg.connect(o2.frequency);o1.connect(f);o2.connect(f);f.connect(g);g.connect(master);o1.start();o2.start();lfo.start();EV.buzz={g,o:[o1,o2,lfo]};}
function stopBuzz(){if(!EV.buzz)return;const b=EV.buzz;EV.buzz=null;try{b.g.gain.setTargetAtTime(0,AC.currentTime,0.08);b.o.forEach(o=>o.stop(AC.currentTime+0.5));}catch(e){}}

// the warning line under the message, with an arrow pointing at the threat
const alertEl=$('alert');
function evAlert(msg){EV.msg=msg;}
function evArrow(x,z){camera.getWorldDirection(projV);let a=Math.atan2(x-P.x,z-P.z)-Math.atan2(projV.x,projV.z);a=Math.atan2(Math.sin(a),Math.cos(a));
  const d=Math.abs(a);return d<0.45?'↑':d>2.6?'↓':a>0?(d<1.4?'↖':'←'):(d<1.4?'↗':'→');}
function evEnd(){const e=EV.cur;if(!e)return;for(const k of EV_KINDS){evM[k].g.visible=false;}evM.branch.shadow.visible=false;stopBuzz();EV.cur=null;EV.msg='';EV.t=38+Math.random()*32;}
const _evA=new THREE.Vector3(),_evB=new THREE.Vector3();

// pick a spot on open ground: not in the gorge, not on a cliff or bridge, not in water
function evGroundOK(x,z){return x>MAP.x0+5&&x<MAP.x1-5&&z>MAP.z0+5&&z<MAP.z1-5&&Math.abs(z-canyonZ(x))>CAN.floorHW+16&&!isCliffFeature(x,z)&&!bridgeAt(x,z)&&!inWater(x,z,groundH(x,z)+0.5);}
function evStart(kind,fx,fz,rx,rz){
  const mvx=P.speed>0.5?P.vx/P.speed:fx,mvz=P.speed>0.5?P.vz/P.speed:fz;   // where you are heading
  const e={kind,t:0,phase:'warn',hit:false};
  if(kind==='magpie'){
    const side=Math.random()<0.5?-1:1;e.side=side;e.x=P.x+rx*side*26+fx*8;e.z=P.z+rz*side*26+fz*8;e.y=P.y+13;e.vx=0;e.vy=0;e.vz=0;
    playCaw();toast('까치가 라디오를 노려요!',2.2);evAlert('까치! 쳐다보면 달아나요 · 아니면 부딪히기 직전 '+(side>0?'E':'Q'));   // a bird from the right knocks the radio left: lean right (E)
  }else if(kind==='boar'){
    let ok=false;for(const side of (Math.random()<0.5?[-1,1]:[1,-1])){const x=P.x+rx*side*23+mvx*5,z=P.z+rz*side*23+mvz*5;if(evGroundOK(x,z)&&groundH(x,z)-P.y<14){e.x=x;e.z=z;ok=true;break;}}
    if(!ok)return false;
    e.dx=P.x-e.x;e.dz=P.z-e.z;const l=Math.hypot(e.dx,e.dz);e.dx/=l;e.dz/=l;e.run=0;
    playGrunt();toast('멧돼지가 노려봐요!',2.2);evAlert('멧돼지가 곧 돌진해요 · 앞뒤로 비켜서세요');
  }else if(kind==='wasps'){
    const s=(Math.random()-0.5)*6;e.x=P.x+mvx*6.5+rx*s;e.z=P.z+mvz*6.5+rz*s;e.y=groundH(e.x,e.z)+2.6;
    startBuzz();playCrunch();toast('말벌집을 건드렸어요!',2.2);evAlert('말벌 떼! 달려서(Shift) 따돌리세요');
  }else if(kind==='branch'){
    const lead=1.6;e.x=P.x+P.vx*lead;e.z=P.z+P.vz*lead;if(!evGroundOK(e.x,e.z)){e.x=P.x;e.z=P.z;}
    e.gy=groundH(e.x,e.z);e.rot=Math.random()*6.3;playCrack();toast('머리 위에서 우지끈!',2);evAlert('가지가 떨어져요! 그림자 밖으로');
  }else if(kind==='snake'){
    const x=P.x+mvx*6,z=P.z+mvz*6;if(!evGroundOK(x,z)||stepAt(x,z)>=0)return false;
    e.x=x;e.z=z;e.h=Math.atan2(-mvx,-mvz)+(Math.random()-0.5)*0.6;   // lies across your way, slowly crossing it
    playHiss();toast('발밑에 뱀이 있어요!',2.2);evAlert('뱀! 가까이 가지 말고 돌아가세요');
  }
  EV.cur=e;EV.last=kind;EV.n++;return true;
}
function updateEvents(dt,playing,fx,fz,rx,rz,brNow,wet,zt){
  const e=EV.cur;
  if(!e){
    // count down only while you're carrying the radio on ordinary footing
    if(!playing||R.state!=='carried'||P.grace>0)return;
    EV.t-=dt;if(EV.t>0)return;
    if(brNow||wet||P.stair>=0||zt===Z_ROCKFALL||Math.abs(P.z-canyonZ(P.x))<CAN.floorHW+22||Math.hypot(P.x-SUMMIT_X,P.z-SUMMIT_Z)<45){EV.t=4;return;}
    const pool=EV_KINDS.filter(k=>k!==EV.last);
    for(let tries=0;tries<4;tries++){if(evStart(pool[Math.floor(Math.random()*pool.length)],fx,fz,rx,rz))return;}
    EV.t=5;return;
  }
  e.t+=dt;
  if(!playing){evEnd();return;}
  const carried=R.state==='carried';
  if(e.kind==='magpie'){
    const m=evM.magpie;m.g.visible=true;const flap=Math.sin(clock*(e.phase==='dive'?9:16))*0.8;m.wl.rotation.z=flap;m.wr.rotation.z=-flap;
    radio.getWorldPosition(_evA);
    if(e.phase==='warn'){e.x+=Math.cos(clock*2)*dt*4;e.z+=Math.sin(clock*2)*dt*4;if(e.t>1.6){e.phase='dive';if(AC)playCaw();}}
    else if(e.phase==='dive'){
      _evB.set(_evA.x-e.x,_evA.y-e.y,_evA.z-e.z);const d=_evB.length();_evB.multiplyScalar(1/Math.max(d,1e-3));
      e.vx=_evB.x*15;e.vy=_evB.y*15;e.vz=_evB.z*15;
      // look it in the eye and it sheers off (turning to face it swings the radio, though)
      camera.getWorldDirection(projV);_evB.set(e.x-camera.position.x,e.y-camera.position.y,e.z-camera.position.z).normalize();
      if(d<20&&d>3&&projV.dot(_evB)>0.9){e.phase='leave';e.vy=9;e.vx*=-0.4;e.vz*=-0.4;toast('까치가 놀라 달아났어요',1.6);EV.msg='';}
      else if(d<0.7||e.t>9){e.phase='leave';EV.msg='';
        if(carried&&d<0.7){const push=Math.sign(e.vx*rx+e.vz*rz)||e.side*-1,resist=clamp(-P.side*push,0,1);   // hold Q/E against the hit
          B.rv+=push*3.0*(1-0.7*resist);B.pv+=0.3;playThud(2.5);playCaw();toast('까치가 라디오를 쪼았어요!',1.8);}
        e.vy=8;}
    }else{e.vy-=dt*2;if(e.t>12||e.y-P.y>40)evEnd();}
    if(e.phase!=='warn'){e.x+=e.vx*dt;e.y+=e.vy*dt;e.z+=e.vz*dt;}else e.y=lerp(e.y,P.y+13,dt);
    if(!EV.cur)return;
    m.g.position.set(e.x,e.y,e.z);const hv=Math.hypot(e.vx,e.vz);m.g.rotation.set(-Math.atan2(e.vy,Math.max(hv,0.1))*0.8,e.phase==='warn'?clock*2+Math.PI/2:Math.atan2(e.vx,e.vz),0);
    if(EV.msg)EV.arrow=evArrow(e.x,e.z);
  }else if(e.kind==='boar'){
    const m=evM.boar;m.g.visible=true;
    if(e.phase==='warn'){
      // pawing the ground, head low
      m.legs[0].rotation.x=Math.max(0,Math.sin(e.t*9))*-0.9;m.head.rotation.x=0.25+Math.sin(e.t*4)*0.08;
      if(e.t>1.0&&!e.g2){e.g2=true;playGrunt();}
      if(e.t>2.1){e.phase='charge';e.dx=P.x-e.x;e.dz=P.z-e.z;const l=Math.hypot(e.dx,e.dz)||1;e.dx/=l;e.dz/=l;playRumble();playGrunt();EV.msg='멧돼지 돌진!';}
    }else{
      const v=e.phase==='charge'?10.5:7;e.x+=e.dx*v*dt;e.z+=e.dz*v*dt;e.run+=v*dt;
      const a=e.t*18;m.legs.forEach((l,i)=>l.rotation.x=Math.sin(a+(i%2?0:Math.PI)+(i>1?1.2:0))*0.8);m.head.rotation.x=0.35;
      if(!e.hit&&Math.hypot(e.x-P.x,e.z-P.z)<1.25&&Math.abs(groundH(e.x,e.z)-P.y)<1.5){e.hit=true;EV.msg='';
        P.vx+=e.dx*6;P.vz+=e.dz*6;P.busy=0.6;playThud(5);playGrunt();
        if(carried){B.pitch=0.25;B.roll=0.95*(Math.sign(e.dx*rx+e.dz*rz)||1);dropRadio();toast('멧돼지에 받혔어요!',2.2);}}
      if(e.run>16&&!e.hit&&EV.msg){EV.msg='';toast('멧돼지를 피했어요',1.4);}
      if(e.run>55||e.t>9||isCliffFeature(e.x,e.z)&&e.run>20){evEnd();return;}
    }
    m.g.position.set(e.x,groundH(e.x,e.z)+(e.phase==='charge'?Math.abs(Math.sin(e.t*18))*0.12:0),e.z);m.g.rotation.y=Math.atan2(e.dx,e.dz);
    if(EV.msg)EV.arrow=evArrow(e.x,e.z);
  }else if(e.kind==='wasps'){
    const m=evM.wasps;m.g.visible=true;
    const tx=P.x,ty=P.y+1.7,tz=P.z,dx=tx-e.x,dy=ty-e.y,dz=tz-e.z,d=Math.hypot(dx,dy,dz);
    if(e.phase==='warn'){if(e.t>0.9)e.phase='chase';}
    else if(e.phase==='chase'){const v=5.7;e.x+=dx/d*v*dt;e.y+=dy/d*v*dt;e.z+=dz/d*v*dt;
      if(d<1.1){e.phase='leave';e.t=0;EV.msg='';P.busy=0.4;playCrunch();
        if(carried){const s=Math.random()<0.5?-1:1;B.rv+=s*2.5;B.pv+=0.8;toast('벌에 쏘였어요! 움찔!',1.8);}}
      else if(e.t>5.5){e.phase='leave';e.t=0;EV.msg='';toast('말벌을 따돌렸어요',1.4);}}
    else{e.y+=dt*1.5;if(e.t>1.4){evEnd();return;}}
    const sc=e.phase==='warn'?e.t/0.9:e.phase==='leave'?1-e.t/1.4:1;
    m.g.position.set(e.x,e.y,e.z);m.g.scale.setScalar(Math.max(0.05,sc));
    for(const b of m.bees){b.a+=dt*b.s;b.b+=dt*b.s*0.7;b.m.position.set(Math.cos(b.a)*b.r,Math.sin(b.b)*b.r*0.6,Math.sin(b.a)*b.r);b.m.rotation.y=b.a+1.57;}
    if(EV.buzz&&AC)EV.buzz.g.gain.setTargetAtTime((muted?0:0.2)*clamp(1-d/30,0.1,1)*Math.max(0.05,sc),AC.currentTime,0.05);
    if(EV.msg)EV.arrow=evArrow(e.x,e.z);
  }else if(e.kind==='branch'){
    const m=evM.branch,T=2.0,R0=1.75;m.g.visible=true;m.shadow.visible=e.phase!=='down';
    if(e.phase==='warn'){
      const h=e.t<0.6?13+Math.sin(e.t*40)*0.1:Math.max(0,13-0.5*(13*2/((T-0.6)*(T-0.6)))*(e.t-0.6)*(e.t-0.6));
      m.g.position.set(e.x,e.gy+0.2+h,e.z);m.g.rotation.set(e.t<0.6?Math.sin(e.t*30)*0.05:(e.t-0.6)*0.8,e.rot,0);
      m.shadow.position.set(e.x,e.gy+0.12,e.z);m.shadow.scale.setScalar(R0*(0.6+0.4*Math.min(1,e.t/T)));m.shadow.material.opacity=0.55*Math.min(1,e.t/0.8);
      if(e.t>=T){e.phase='down';e.t=0;EV.msg='';playThud(6);playCrunch();m.g.position.y=e.gy+0.18;m.g.rotation.x=0;
        const d=Math.hypot(P.x-e.x,P.z-e.z);
        if(carried&&d<R0){B.pitch=0.9;dropRadio();toast('떨어진 가지에 맞았어요!',2.2);P.busy=0.4;}
        else if(carried&&d<R0+1.4){B.pv+=0.7;B.rv+=(Math.random()-.5)*1.4;toast('아슬아슬하게 피했어요',1.4);}
        else toast('가지를 피했어요',1.2);}
    }else{if(e.t>9){m.g.position.y-=dt*0.6;}if(e.t>11){evEnd();return;}}
    if(EV.msg)EV.arrow=evArrow(e.x,e.z);
  }else if(e.kind==='snake'){
    const m=evM.snake;m.g.visible=true;const d=Math.hypot(P.x-e.x,P.z-e.z);
    const spd=e.phase==='leave'?2.2:0.25;e.x+=Math.cos(e.h)*spd*dt;e.z-=Math.sin(e.h)*spd*dt;
    if(e.phase==='warn'){
      if(d<2.1){e.phase='leave';e.t=0;EV.msg='';playHiss();
        // you jump back from it: the radio tips hard backwards (Space to catch it)
        const ax=(P.x-e.x)/(d||1),az=(P.z-e.z)/(d||1);P.vx=ax*3.2;P.vz=az*3.2;P.busy=0.45;
        if(carried){B.pv+=1.5*(1-0.55*P.lean);B.rv+=(Math.random()-.5)*0.6;toast('뱀에 놀라 뒷걸음질!',1.8);}}
      else if(e.t>16||d>40){evEnd();return;}
      else if(d>9&&e.t>4&&EV.msg){EV.msg='';}
    }else if(e.t>2.5){evEnd();return;}
    // slither: each bead follows a sine wave along the body
    const ch=Math.cos(e.h),sh=-Math.sin(e.h);
    m.segs.forEach((s,i)=>{const back=i*0.08,w=Math.sin(clock*(e.phase==='leave'?14:5)-i*0.7)*0.12*Math.min(1,i/3);
      const x=e.x-ch*back-sh*w,z=e.z-sh*back+ch*w;s.position.set(x,groundH(x,z)+0.06+(i===0&&e.phase==='warn'?0.12+Math.sin(clock*3)*0.03:0),z);s.rotation.y=Math.atan2(ch,sh);});
    if(EV.msg)EV.arrow=evArrow(e.x,e.z);
  }
}

function update(dt){
  if(!(dt>0))return;
  clock+=dt;
  const playing=game==='play';
  if(playing)elapsed+=dt;
  // input
  let fwdIn=((k('KeyW')||k('ArrowUp'))?1:0)-((k('KeyS')||k('ArrowDown'))?1:0);
  let strafeIn=((k('KeyD')||k('ArrowRight'))?1:0)-((k('KeyA')||k('ArrowLeft'))?1:0);   // 옆걸음
  const runT=playing&&(k('ShiftLeft')||k('ShiftRight'));            // 달리기
  const leanT=playing&&R.state==='carried'&&k('Space')?1:0;         // 몸 숙이기
  const sideT=playing?((k('KeyE')?1:0)-(k('KeyQ')?1:0)):0;
  if(!playing||P.busy>0){fwdIn=0;strafeIn=0;}
  P.busy=Math.max(0,P.busy-dt);
  P.lean+=(leanT-P.lean)*Math.min(1,dt*7);
  P.side+=(sideT-P.side)*Math.min(1,dt*7);

  // where are we?
  const zi=zoneAt(P.x,P.z),zt=zi.type,zw=zi.w;
  const brNow=bridgeAt(P.x,P.z,P.y),bridgeNow=!!brNow,stairNow=stepAt(P.x,P.z),wet=inWater(P.x,P.z,P.y);
  const zone=zw>0.45?zt:-1;
  if(zone>=0&&zone!==P.zone&&playing){P.zone=zone;toast(ZONES[zone].name+' · '+ZONES[zone].desc,3);}
  if(zone<0&&zw<0.15)P.zone=-1;
  if(brNow&&P.wasBridge!==brNow&&playing)toast(brNow.K.toast,2.2);
  P.wasBridge=brNow||false;
  if(wet&&!P.wasWet&&playing)toast('물살 · 발이 느려지고 미끄러워요',2);
  P.wasWet=wet;

  // the body faces where you look; the mouse sets P.yaw directly
  const fx=Math.sin(P.yaw),fz=Math.cos(P.yaw),rx=-Math.cos(P.yaw),rz=Math.sin(P.yaw);
  if(brNow&&brNow.kind==='log')strafeIn*=0.3;   // on the log, A/D are small careful side-steps
  let mx=fx*fwdIn+rx*strafeIn,mz=fz*fwdIn+rz*strafeIn;const ml=Math.hypot(mx,mz);if(ml>0){mx/=ml;mz/=ml;}
  const mScale=(brNow&&brNow.kind==='log'&&fwdIn===0)?0.3:1;
  const hereSlope=(bridgeNow||stairNow>=0)?0:slopeAt(P.x,P.z);
  const mGrade=ml>0?(surfaceH(P.x+mx*0.6,P.z+mz*0.6,P.y)-surfaceH(P.x-mx*0.6,P.z-mz*0.6,P.y))/1.2:0;
  const sideSlope=bridgeNow?0:(groundH(P.x+rx*0.5,P.z+rz*0.5)-groundH(P.x-rx*0.5,P.z-rz*0.5))/1.0;
  let maxSpd=(runT&&fwdIn>0?6.8:4.4)*(hereSlope>0.6?0.75:1)*(1-P.lean*0.5);
  if(fwdIn<0)maxSpd=Math.min(maxSpd,1.8);else if(fwdIn===0&&strafeIn!==0)maxSpd=Math.min(maxSpd,2.8);
  maxSpd*=clamp(1-Math.max(0,mGrade)*1.1,0.3,1);
  if(zt===Z_STEEP)maxSpd*=lerp(1,0.6,zw);
  if(zt===Z_SCREE)maxSpd*=lerp(1,0.75,zw);
  const offStairs=zt===Z_STAIRS&&zw>0.35&&stairNow<0&&!bridgeNow;   // stairs patch, but not on the steps
  if(offStairs)maxSpd*=lerp(1,0.6,zw);
  if(zt===Z_MUD)maxSpd=Math.min(maxSpd,lerp(maxSpd,1.6,zw));     // knee-deep: no running
  if(wet)maxSpd*=0.5;
  // cliffs and canyon walls can't be climbed: go round, or find the gap, the ford or the bridge
  const wall=ml>0&&mGrade>1.45&&!bridgeNow&&isCliffFeature(P.x+mx*0.6,P.z+mz*0.6);
  if(wall){maxSpd=0;if(toastT<=0&&playing)toast('절벽이라 오를 수 없어요. 다른 길을 찾으세요',2.2);}
  const tvx=ml>0?mx*maxSpd*mScale:0,tvz=ml>0?mz*maxSpd*mScale:0;
  const pvx=P.vx,pvz=P.vz;
  // traction: mossy rock and water barely let you speed up, slow down or turn
  const speedingUp=Math.hypot(tvx,tvz)>Math.hypot(P.vx,P.vz);
  const grip=(zt===Z_MOSS?lerp(1,speedingUp?0.3:0.09,zw):1)*(zt===Z_MUD?lerp(1,0.5,zw):1)*(wet?0.45:1);   // on moss you get going slowly and stop even more slowly
  {let dvx=tvx-P.vx,dvz=tvz-P.vz;const dvl=Math.hypot(dvx,dvz),rate=(speedingUp?4.5:7)*grip*dt;
   if(dvl>rate&&dvl>1e-9){dvx*=rate/dvl;dvz*=rate/dvl;}P.vx+=dvx;P.vz+=dvz;}
  if(zt===Z_MOSS&&zw>0.4&&P.speed>1&&Math.random()<dt*0.9){const s=(Math.random()-.5)*3.2;P.vx+=rx*s;P.vz+=rz*s;}   // a foot slips sideways
  if(!isFinite(P.vx)||!isFinite(P.vz)){P.vx=0;P.vz=0;}
  if(!isFinite(P.x)||!isFinite(P.z)){P.x=START_X;P.z=START_Z;}
  {const ax=(P.vx-pvx)/Math.max(dt,1e-3),az=(P.vz-pvz)/Math.max(dt,1e-3);
   P.accel=lerp(P.accel,ax*fx+az*fz,0.3);P.lat=lerp(P.lat,ax*rx+az*rz,0.3);}
  const mx0=P.x,mz0=P.z;
  P.x+=P.vx*dt;P.z+=P.vz*dt;
  // loose ground: scree slides you down; on the steep pitch you slide back unless you keep climbing
  if(!bridgeNow&&stairNow<0){
    if(offStairs){downhill(P.x,P.z,_dh);const s=zw*(0.6+0.8*Math.min(1,slopeAt(P.x,P.z)))*(fwdIn>0?0.35:1);P.x+=_dh.x*s*dt;P.z+=_dh.z*s*dt;}   // loose rock beside the stairs
    if(zt===Z_SCREE&&zw>0.2){downhill(P.x,P.z,_dh);const s=zw*(0.5+0.7*Math.min(1,slopeAt(P.x,P.z)))*(fwdIn>0?0.3:1);   /* slides you down when you stop; keep walking and it only drags a little */P.x+=_dh.x*s*dt;P.z+=_dh.z*s*dt;}
    if(zt===Z_STEEP&&zw>0.2&&fwdIn<=0){downhill(P.x,P.z,_dh);const s=1.8*zw*Math.min(1,slopeAt(P.x,P.z)*1.5);P.x+=_dh.x*s*dt;P.z+=_dh.z*s*dt;}
  }
  // fallen logs: stepping over one slows you and jolts the load
  let logHit=0;
  gridEach(logG,P.x,P.z,L=>{if(clock-L.hitT<1.0)return;   /* a log sits in several grid cells: time-stamp, not a countdown */const ox=P.x-L.x,oz=P.z-L.z,al=ox*L.dx+oz*L.dz,pe=Math.abs(-ox*L.dz+oz*L.dx);
    if(Math.abs(al)<L.half&&pe<0.45&&P.speed>0.3){L.hitT=clock;logHit=Math.max(logHit,P.speed);P.vx*=0.55;P.vz*=0.55;hips.position.y=1.06;}});
  // hidden holes under the leaves
  let holeHit=false;
  if(zt===Z_LEAF)gridEach(holeG,P.x,P.z,o=>{o.cd=Math.max(0,o.cd-dt);if(o.cd>0)return;if(Math.hypot(P.x-o.x,P.z-o.z)<0.62&&P.speed>0.2){o.cd=4;holeHit=true;P.vx*=0.2;P.vz*=0.2;hips.position.y=0.6;}});
  if(holeHit){playCrunch();if(playing&&toastT<=0.6)toast('낙엽 밑 구덩이에 발이 빠졌어요!',1.8);}
  // mud: every step sucks at your boots
  let mudStep=false;{const ms=Math.floor(P.step/Math.PI);if(ms!==P.mudStep){P.mudStep=ms;mudStep=zt===Z_MUD&&zw>0.4&&P.speed>0.3;if(mudStep&&Math.random()<0.6)playSquelch();}}
  // rockfall: boulders come rolling down the slope at you
  if(playing&&zt===Z_ROCKFALL&&zw>0.3&&R.state==='carried'&&P.grace<=0){RF.t-=dt;   /* no new boulders while you're fetching the radio or just picked it up */if(RF.t<=0){RF.t=2.2+Math.random()*2.5;const r=ROCKS.find(r=>!r.on);
    if(r){downhill(P.x,P.z,_dh);const lat=(Math.random()-0.5)*7;r.x=P.x-_dh.x*26-_dh.z*lat;r.z=P.z-_dh.z*26+_dh.x*lat;/* aimed at where you stand now: step aside to dodge */{const ax=P.x-r.x,az=P.z-r.z,al=Math.hypot(ax,az)||1;r.dx=ax/al;r.dz=az/al;}r.vx=0;r.vz=0;r.life=8;r.hit=false;r.on=true;r.m.visible=true;playRumble();if(toastT<=0.6)toast('낙석! 굴러오는 돌을 피하세요',1.6);}}}
  for(const r of ROCKS){if(!r.on)continue;r.life-=dt;const k2=1-Math.exp(-dt*2.5);r.vx=lerp(r.vx,r.dx*6.2,k2);r.vz=lerp(r.vz,r.dz*6.2,k2);r.x+=r.vx*dt;r.z+=r.vz*dt;
    const ry=groundH(r.x,r.z)+0.75+Math.abs(Math.sin(r.life*6))*0.4;r.m.position.set(r.x,ry,r.z);r.m.rotation.x+=dt*Math.hypot(r.vx,r.vz)/0.8;r.m.rotation.y=Math.atan2(r.vx,r.vz);
    if(r.life<=0||r.x<MAP.x0||r.x>MAP.x1||r.z<MAP.z0||r.z>MAP.z1){r.on=false;r.m.visible=false;continue;}
    if(!r.hit&&playing&&Math.hypot(r.x-P.x,r.z-P.z)<1.3&&Math.abs(ry-P.y-1)<2.2){r.hit=true;P.vx+=r.vx*0.5;P.vz+=r.vz*0.5;playThud(4);
      if(R.state==='carried'){B.pitch=0.9;dropRadio();toast('굴러온 돌에 맞았어요!',2);}RF.t=Math.max(RF.t,4);}}
  // one-off hazards (magpie, boar, wasps, branch, snake)
  updateEvents(dt,playing,fx,fz,rx,rz,brNow,wet,zt);
  // wind gusts on the ridges also shove you a little
  if(zt===Z_WIND&&WIND.on>0){P.x+=WIND.x*0.5*zw*dt;P.z+=WIND.z*0.5*zw*dt;}
  // trees and big rocks block the way
  gridEach(blockG,P.x,P.z,o=>{const ox=P.x-o.x,oz=P.z-o.z,d=Math.hypot(ox,oz),min=o.r+0.32;
    if(d<min&&d>1e-4){const nx=ox/d,nz=oz/d;P.x=o.x+nx*min;P.z=o.z+nz*min;const vn=P.vx*nx+P.vz*nz;if(vn<0){P.vx-=vn*nx;P.vz-=vn*nz;}}});
  // the bridge has rope rails
  if(brNow&&brNow.K.rail>0&&P.z>brNow.z0+0.6&&P.z<brNow.z1-0.6){const lim=brNow.K.rail,cx=bridgeCenterX(brNow,P.z);if(Math.abs(P.x-cx)>lim){P.x=cx+Math.sign(P.x-cx)*lim;P.vx*=0.3;}}
  // the single log rolls under your feet and nudges you sideways; no rails
  if(brNow&&brNow.kind==='log')P.x+=fbm(clock*0.8,brNow.x)*0.8*dt*(0.6+P.speed*0.35);
  P.x=clamp(P.x,MAP.x0,MAP.x1);P.z=clamp(P.z,MAP.z0,MAP.z1);
  const prevY=P.y;
  // at the ends of the rope and stone bridges, the gorge edge beside the deck is fenced off:
  // you can't step off sideways into the canyon there (the single log has no such help)
  {const onDeck=bridgeAt(P.x,P.z,prevY);
   if(!onDeck){const ny=surfaceH(P.x,P.z,prevY),edge=prevY-ny>2||(slopeAt(P.x,P.z)>1.4&&isCliffFeature(P.x,P.z));
     if(edge)for(const b of BRIDGES){if(b.kind==='log')continue;const nearEnd=Math.abs(P.x-b.x)<6&&(Math.abs(P.z-b.z0)<7||Math.abs(P.z-b.z1)<7);
       if(nearEnd){P.x=mx0;P.z=mz0;P.vx=0;P.vz=0;break;}}}}
  P.y=surfaceH(P.x,P.z,prevY);
  // stepping off a bridge (or any sudden drop): you land hard and the radio flies off
  if(playing&&prevY-P.y>2.5&&R.state==='carried'){B.pitch=0.9;dropRadio();toast(P.wasBridge?'다리에서 떨어졌어요!':'높은 데서 떨어졌어요!',2.4);}
  // stepping off a cliff edge: you tumble down and the radio goes flying
  if(!bridgeNow&&stairNow<0&&slopeAt(P.x,P.z)>1.7&&isCliffFeature(P.x,P.z)){
    downhill(P.x,P.z,_dh);P.vx=_dh.x*4;P.vz=_dh.z*4;
    if(R.state==='carried'&&playing){B.pitch=0.9;dropRadio();toast('절벽에서 미끄러졌어요!',2.4);}
  }
  P.speed=Math.hypot(P.vx,P.vz);
  P.step+=P.speed*dt*2.3;
  const vGrade=P.speed>0.1?(surfaceH(P.x+P.vx/P.speed*0.6,P.z+P.vz/P.speed*0.6,P.y)-surfaceH(P.x-P.vx/P.speed*0.6,P.z-P.vz/P.speed*0.6,P.y))/1.2:0;
  // mouse turning speed: a slow look is harmless, shaking the view left-right is not
  {let dy=P.yaw-P.yawPrev;dy=Math.atan2(Math.sin(dy),Math.cos(dy));P.yawPrev=P.yaw;
   P.yawVel=lerp(P.yawVel,dy/dt,0.5);P.shake=lerp(P.shake,Math.abs(P.yawVel),1-Math.exp(-dt/0.35));}
  const stairChanged=stairNow>=0&&P.stair>=0&&stairNow!==P.stair;P.stair=stairNow;

  // the rope bridge swings; walking pumps it, running pumps it hard
  for(const br of BRIDGES){if(br.kind!=='rope')continue;const on=brNow===br;let drive=0;if(on&&P.speed>0.3)drive=Math.sin(P.step*0.5)*P.speed*P.speed*0.09;
   const cxOld=on?bridgeCenterX(br,P.z):0,rxOld=(R.state==='ground'&&bridgeAt(R.pos.x,R.pos.z,R.pos.y)===br)?bridgeCenterX(br,R.pos.z):null;
   br.vel+=(-14*br.ang-0.35*br.vel+drive)*dt;br.ang=clamp(br.ang+br.vel*dt,-0.3,0.3);
   if(on){const dx=bridgeCenterX(br,P.z)-cxOld;P.x+=dx;          // the deck carries you sideways as it swings
     const v=dx/dt;P.deckAcc=lerp(P.deckAcc,(v-P.deckVel)/dt,0.35);P.deckVel=v;}
   if(rxOld!==null)R.pos.x+=bridgeCenterX(br,R.pos.z)-rxOld;
   br.bob=lerp(br.bob,on?-0.35-Math.abs(Math.sin(P.step))*0.12:0,0.1);
   for(const m of br.group.children){const d=m.userData,roll=bridgeRoll(br,d.z),off=bridgeCenterX(br,d.z)-br.x;
     m.position.x=d.bx+off-d.above*Math.sin(roll);m.position.y=d.by+d.bx*Math.sin(roll)+br.bob*bridgeSpanU(br,d.z);m.rotation.z=roll;}}
  if(!brNow||brNow.kind!=='rope'){P.deckVel*=0.8;P.deckAcc*=0.8;}
  // gust timer (only matters on the ridges)
  WIND.t-=dt;
  if(WIND.on>0){WIND.on-=dt;const ph=1-WIND.on/WIND.dur;WIND.str=Math.sin(ph*Math.PI)*WIND.peak;WIND.x=Math.cos(WIND.dir)*WIND.str;WIND.z=Math.sin(WIND.dir)*WIND.str;if(WIND.on<=0){WIND.str=0;WIND.x=WIND.z=0;}}
  else if(WIND.t<=0){WIND.dur=1.4+Math.random()*1.2;WIND.on=WIND.dur;WIND.peak=1.2+Math.random()*0.7;WIND.dir=Math.random()*Math.PI*2;WIND.t=3.5+Math.random()*3.5;
    if(zt===Z_WIND&&zw>0.3&&playing){playGust();}}

  // balance
  if(R.state==='carried'&&playing){
    const sp=P.speed;
    let fp=0,fr=0;const pv0=B.pv;
    fp+=clamp(P.accel*0.085,-0.4,0.4);
    fp+=vGrade*sp*0.55;
    fp+=Math.sin(P.step*2)*sp*0.03;
    if(sp>4.8){const rs=(sp-4.4)/2.4;fp+=Math.abs(Math.sin(P.step*2))*0.4*rs;fr+=Math.sin(P.step)*0.3*rs;} // 달리면 라디오가 크게 출렁인다
    fp+=fbm(clock*0.9,3.3)*0.3*(sp/4.4);
    fp-=P.lean*1.5;
    fr+=clamp(-P.lat*0.085,-0.36,0.36);   // sideways shove when you change walking direction (a little stronger)
    fr-=sideSlope*0.6*Math.min(1,sp/4.4);
    fr+=fbm(clock*0.8,17.1)*0.4*(sp/4.4);
    fr+=P.side*1.05;
    if(sp>0.5&&Math.random()<dt*1.4){const rough=hereSlope>0.6?0.9:0.45;B.pv+=(Math.random()*0.8)*rough*(sp/4.4);B.rv+=(Math.random()-.5)*1.1*rough*(sp/4.4);}
    // every stair step bumps the radio; running up stairs is asking for trouble
    if(stairChanged&&sp>0.3){const imp=0.06+0.014*sp*sp;B.pv+=imp*(0.8+Math.random()*0.4);B.rv+=(Math.random()-.5)*imp*0.8;hips.position.y=0.99;}
    // off the stairs in a stairs patch: broken rock throws the load about
    if(offStairs&&Math.random()<dt*3.5*zw){const s=0.45+sp/4.4*0.5;B.pv+=Math.random()*0.6*s;B.rv+=(Math.random()-.5)*1.2*s;}
    // scree: the ground keeps shoving the load around
    if(zt===Z_SCREE&&zw>0.3&&Math.random()<dt*3*zw){const s=0.35+sp/4.4*0.4;B.pv+=Math.random()*0.5*s;B.rv+=(Math.random()-.5)*0.9*s;}
    // water: the current tugs at you
    if(wet&&Math.random()<dt*1.5){B.rv+=(Math.random()-.5)*0.7;B.pv+=Math.random()*0.25;}
    if(logHit){const imp=0.18+0.035*logHit*logHit;B.pv+=imp*(0.8+Math.random()*0.4);B.rv+=(Math.random()-.5)*imp;}
    if(holeHit){B.pv+=0.5+Math.random()*0.3;B.rv+=(Math.random()-.5)*0.9;}
    if(mudStep){B.pv+=0.08+Math.random()*0.14;B.rv+=(Math.random()-.5)*0.28;}
    // waterfall spray
    {const d=Math.hypot(P.x-WF.x,P.z-WF.zBot);if(d<22&&P.y<WF.yBot+6&&Math.random()<dt*2)B.rv+=(Math.random()-.5)*0.9*(1-d/22);}
    // windy ridge: gusts lean the radio away from the wind (hold it with Q/E, or turn into the wind)
    if(zt===Z_WIND&&WIND.on>0){const wr=WIND.x*rx+WIND.z*rz,wf=WIND.x*fx+WIND.z*fz;fr+=wr*0.62*zw;fp+=-wf*0.4*zw;}
    // the rope bridge rolls the radio with it
    // rope bridge: the radio rides the deck. Every lurch of the deck flings it the other way,
    // the deck's tilt leans it, and the bouncing deck jolts it back
    if(brNow&&brNow.kind==='rope'){const sp2=bridgeSpanU(brNow,P.z);
      fr+=clamp(-P.deckAcc*0.12,-0.85,0.85)+bridgeRoll(brNow,P.z)*3.5+(brNow.ang*2.5+brNow.vel*0.3)*(0.3+0.7*sp2);
      fp+=Math.min(0.5,Math.abs(P.deckAcc)*0.04+Math.abs(brNow.vel)*0.1*sp2);
      if(sp>4.8)fr+=Math.sin(P.step)*0.55*sp2;}   // running thumps the deck under you
    if(brNow&&brNow.kind==='log'){fr+=(P.x-brNow.x)*1.6+fbm(clock*1.6,brNow.x+3)*0.6;}   // off-centre on the log, the load leans out
    // turning the view swings the radio: it leans out of every turn, a sudden flick kicks it,
    // and shaking the view left-right pumps it over within a second or so
    {const dw=P.yawVel-P.yawVelPrev;P.yawVelPrev=P.yawVel;B.rv+=clamp(-dw*0.07,-0.45,0.45);
     fr+=clamp(P.yawVel*0.1,-0.4,0.4);
     if(P.shake>1.6){const ex=P.shake-1.6,dir=Math.abs(B.roll)>0.02?Math.sign(B.roll):(Math.sign(P.yawVel)||1);fr+=dir*ex*0.75;fp+=ex*0.18;}}
    for(const b of bumpsNear(P.x,P.z)){b.cd=Math.max(0,b.cd-dt);if(b.cd>0)continue;const dx=b.x-P.x,dz=b.z-P.z;if(dx*dx+dz*dz<0.55&&sp>0.4){b.cd=1.5;const sev=lerp(0.55,1.05,clamp(P.y/SUMMIT_H,0,1));B.pv+=(0.75+Math.random()*0.5)*sev*(sp/4.4);B.rv+=(Math.random()-.5)*1.4*sev*(sp/4.4);hips.position.y=1.02;}}
    B.pv=pv0+(B.pv-pv0)*0.7;   // bumps, steps and logs tip the radio back 30% less
    if(P.grace>0){P.grace-=dt;fp*=0.35;fr*=0.35;}
    const KF=3.0,K=9,G=6,C=2.6,SAT=0.45,KFP=KF*0.73;   // backward push 27% weaker than sideways
    const pa=KFP*fp-K*clamp(B.pitch,-SAT,SAT)+G*Math.sin(B.pitch)-C*B.pv;
    const ra=KF*fr-K*clamp(B.roll,-SAT,SAT)+G*Math.sin(B.roll)-C*B.rv;
    B.pv+=pa*dt;B.rv+=ra*dt;B.pitch+=B.pv*dt;B.roll+=B.rv*dt;
    if(B.pitch<FWD_LIMIT){B.pitch=FWD_LIMIT;if(B.pv<0)B.pv*=-0.2;}
    if(B.pitch>FALL||Math.abs(B.roll)>FALL)dropRadio();
  }
  if(R.state==='carried'){radioPivot.rotation.set(-B.pitch,0,B.roll);radio.position.y=Math.abs(Math.sin(P.step*2))*0.012*Math.min(1,P.speed);}
  else if(R.state==='falling'){R.squash=Math.max(0,R.squash-dt*4.5);updateRadioPhysics(dt);}
  else if(R.state==='ground'){R.squash=Math.max(0,R.squash-dt*4.5);settleRadio(dt);}
  else if(R.state==='pickup')updatePickup(dt);

  // win check
  const toSummit=Math.hypot(P.x-SUMMIT_X,P.z-SUMMIT_Z);
  if(playing&&toSummit<SUMMIT_R){
    if(R.state==='carried')win();
    else if(toastT<=0)toast('라디오를 두고 왔어요! 다시 가져오세요',2.2);
  }

  // fog in the misty maple forest
  {const target=(playing&&zt===Z_FOG)?zw:0;fogMix=lerp(fogMix,target,1-Math.exp(-dt*1.5));
   scene.fog.near=lerp(220,3,fogMix);scene.fog.far=lerp(1700,38,fogMix);scene.fog.color.setHex(FOG).lerp(_fogC.setHex(FOG_MIST),fogMix);scene.background.copy(scene.fog.color);}
  if(fallTex){fallTex.offset.y-=dt*0.9;fallTex2.offset.y-=dt*1.35;}
  for(let i=0;i<WF.mist.length;i++){const m=WF.mist[i],s=1+0.18*Math.sin(clock*1.3+i*1.7);m.scale.setScalar(m.userData.base*s);m.position.y=m.userData.y+Math.sin(clock*0.8+i)*0.6;m.material.opacity=0.4+0.15*Math.sin(clock*1.1+i*2.3);}

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
const _fogC=new THREE.Color();

function win(){
  game='win';playWin();
  if(document.exitPointerLock&&locked)document.exitPointerLock();updateLookHint();
  const t=fmt(elapsed);$('wTime').textContent=t;$('wDrops').textContent=drops;
  let best=null;try{best=parseFloat(localStorage.getItem('jige-radio-best'));}catch(e){}
  if(!best||elapsed<best){best=elapsed;try{localStorage.setItem('jige-radio-best',String(elapsed));}catch(e){}}
  $('wBest').textContent=fmt(best);
  $('winMsg').textContent=drops===0?'한 번도 떨어뜨리지 않았어요. 라디오 소리가 산 아래 마을까지 울려 퍼집니다.':drops<=3?'몇 번 넘어졌지만 끝까지 지고 왔어요. 정상에서 듣는 라디오가 각별합니다.':'라디오가 '+drops+'번이나 굴렀지만 아직 잘 나옵니다. 튼튼한 라디오예요.';
  setTimeout(()=>{if(game==='win')$('winScreen').hidden=false;},900);
}
function fmt(s){const m=Math.floor(s/60),r=s-m*60;return String(m).padStart(2,'0')+':'+(r<10?'0':'')+r.toFixed(1);}

function updateCamera(dt){
  if(game==='title'){
    titleT+=dt*0.035;const a=titleT-1.2;
    camera.position.set(Math.cos(a)*1050,430,640+Math.sin(a)*950);camera.lookAt(0,90,680);
    camState.pos.copy(camera.position);camState.look.set(0,90,680);return;
  }
  if(game==='win'){ // step back and circle the summit to celebrate
    setBodyVisible(true);
    const yaw=P.yaw+clock*0.25,cx=P.x-Math.sin(yaw)*9,cz=P.z-Math.cos(yaw)*9;
    camState.pos.lerp(_v.set(cx,Math.max(P.y+4,groundH(cx,cz)+1.2),cz),1-Math.exp(-dt*3));
    camera.position.copy(camState.pos);camera.lookAt(P.x,P.y+1.5,P.z);return;
  }
  // first person: eyes at the head (so leaning and walking bob the view), looking where the mouse points
  headMesh.getWorldPosition(_v);
  _v.x+=Math.sin(P.yaw)*0.26;_v.z+=Math.cos(P.yaw)*0.26;_v.y+=0.02;
  _v.y=Math.max(_v.y,groundH(_v.x,_v.z)+0.4);
  camera.position.copy(_v);camState.pos.copy(_v);
  camera.rotation.set(P.pitch,P.yaw+Math.PI,P.wasBridge&&P.wasBridge.kind==='rope'?bridgeRoll(P.wasBridge,P.z)*0.7:0,'YXZ');   // the view rolls with a rope bridge
  const fov=lerp(camera.fov,P.speed>4.8?78:70,1-Math.exp(-dt*3));
  if(Math.abs(fov-camera.fov)>0.01){camera.fov=fov;camera.updateProjectionMatrix();}
}

// ---------------------------------------------------------------- HUD
const lcd=$('lcdText');let lcdMode='';
const projV=new THREE.Vector3();
const compassEl=$('compass');
function updateHUD(){
  if(game==='title')return;
  const t=clamp(P.y/SUMMIT_H,0,1);
  $('prog').style.width=(t*100).toFixed(1)+'%';
  $('alt').textContent='해발 '+Math.round(ALT0+Math.max(0,P.y)*ALT_SCALE)+' m · 정상까지 직선 '+Math.round(Math.hypot(P.x-SUMMIT_X,P.z-SUMMIT_Z))+' m';
  {const zt=P.zone>=0?ZONES[P.zone].name:'산자락';const ze=$('zoneName');if(ze.textContent!==zt)ze.textContent=zt;}
  // compass: arrow points to the summit relative to where the camera looks
  camera.getWorldDirection(projV);
  const rel=Math.atan2(SUMMIT_X-P.x,SUMMIT_Z-P.z)-Math.atan2(projV.x,projV.z);
  compassEl.style.transform='rotate('+(-rel).toFixed(3)+'rad)';
  compassEl.style.visibility=fogMix>0.5?'hidden':'visible';   // the compass is useless in the mist
  $('time').textContent=fmt(elapsed);
  const danger=R.state==='carried'&&Math.hypot(Math.max(0,B.pitch),B.roll)>NO_RETURN*0.85;   // the balance gauge is gone; only its warnings remain
  const lbl=$('gaugeLbl');
  let msg='',warn=false;
  if(R.state==='carried'&&game==='play'){
    if(P.shake>1.6){warn=true;msg='화면을 흔들지 마세요!';}
    else if(P.zone===Z_WIND&&WIND.on>0&&WIND.str>0.5){warn=true;const wr=WIND.x*(-Math.cos(P.yaw))+WIND.z*Math.sin(P.yaw);msg=wr>0?'돌풍! 오른쪽으로 밀려요 Q':'돌풍! 왼쪽으로 밀려요 E';}
    else if(danger){warn=true;msg=B.pitch>Math.abs(B.roll)?'뒤로 넘어가요! Space':(B.roll>0?'오른쪽으로 쏠려요! Q':'왼쪽으로 쏠려요! E');}
  }else if(R.state!=='carried'&&R.state!=='pickup'){msg='라디오를 주우세요';warn=true;}
  if(lbl.textContent!==msg)lbl.textContent=msg;lbl.classList.toggle('warn',warn);
  // radio lcd
  let mode=R.state==='carried'||R.state==='pickup'?(danger?'weak':'ok'):'off';
  if(mode!==lcdMode){lcdMode=mode;lcd.textContent=mode==='ok'?'FM 98.1 ♪ 소리봉 방송':mode==='weak'?'FM 98.1 ~ 지지직…':'-- 신호 약함 --';lcd.classList.toggle('off',mode==='off');}
  // hazard warning with an arrow toward it
  {const on=game==='play'&&!!EV.msg;if(alertEl.hidden===on)alertEl.hidden=!on;if(on){const tx=(EV.arrow||'!')+' '+EV.msg;if(alertEl.textContent!==tx)alertEl.textContent=tx;}}
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
  if(waterGain){const dW=Math.hypot(P.x-WF.x,P.z-(WF.zBot+WF.zTop)/2),dR=Math.abs(P.z-canyonZ(P.x));
    waterGain.gain.setTargetAtTime(game==='title'?0:Math.max(0.45*(1-clamp(dW/140,0,1)),0.16*(1-clamp(dR/70,0,1))),AC.currentTime,0.2);}
}

// ---------------------------------------------------------------- loop
function resize(){renderer.setSize(innerWidth,innerHeight,false);camera.aspect=innerWidth/innerHeight;camera.updateProjectionMatrix();}
addEventListener('resize',resize);
let last=performance.now();
let slowFrames=0,frameCount=0,reportedLoopError=false;
function frame(now){
  requestAnimationFrame(frame);                       // schedule first so one bad frame can't freeze the game
  // the first rAF timestamp can be earlier than performance.now() taken at load: never let dt go negative
  const raw=(now-last)/1000,dt=clamp(isFinite(raw)?raw:0,0,0.05);last=now;
  try{update(dt);updateHUD();updateAudio();}
  catch(err){if(!reportedLoopError){reportedLoopError=true;console.error(err);showError('게임 실행 중 오류가 났어요','새로고침(Ctrl+Shift+R)해 보세요. 계속되면 이 문구를 알려주세요: '+err.message);}}
  if(!isFinite(camera.position.x)||!isFinite(camera.position.y)||!isFinite(camera.position.z)){P.pitch=0;if(!isFinite(P.yaw))P.yaw=0;camera.position.set(P.x,P.y+1.7,P.z);}
  renderer.render(scene,camera);
  // drop resolution, then shadows, if the machine can't keep up
  frameCount++;if(raw>0.045&&raw<1)slowFrames++;
  if(frameCount%120===0){
    if(slowFrames>70){
      if(pixelRatio>0.75){pixelRatio=Math.max(0.75,pixelRatio-0.25);renderer.setPixelRatio(pixelRatio);resize();}
      else if(renderer.shadowMap.enabled){renderer.shadowMap.enabled=false;sun.castShadow=false;scene.traverse(o=>{if(o.material)o.material.needsUpdate=true;});}
    }
    slowFrames=0;
  }
}
document.body.classList.add('title');
reset();
requestAnimationFrame(frame);
window.__game={P,B,R,WIND,LAYOUT_SEED,get state(){return game;},get fog(){return fogMix;},keys,dropRadio,tryPickup,groundH,slopeAt,surfaceH,stepAt,zoneAt,onBridge,bridgeAt,bridgeDeck,deckAt,bridgeCenterX,blockG,gridEach,inWater,canyonZ,canyonFloor,cliffZ,CLIFF,BRIDGES,FORD_X,FALL_X,PATCHES,STEPS,STAIR_STARTS,ZONES,ROCKS,LOGS,HOLES,isCliffFeature,SUMMIT_X,SUMMIT_Z,SUMMIT_H,START_SLOTS,
  step(n,dt,quiet){for(let i=0;i<n;i++)update(dt);if(!quiet){updateHUD();renderer.render(scene,camera);}},start:startGame,EV,triggerEvent(kind){const f=Math.sin(P.yaw),g=Math.cos(P.yaw);evEnd();return evStart(kind,f,g,-g,f);}};
})();
