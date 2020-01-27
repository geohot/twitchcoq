program BBfind;

uses crt , dos;

const dm=5;                  { TM dimension. Must be 2,3,4,5 or 6 }
      reversal={true} false; { Reversal / Normal TM }
      SameDir ={true} false; { Dir(0) = Dir(1) limitation }
      Destructive={true} false;{ Destructive TM: value_1=1 limitation }
      
      slow_scan=true {false}; { slow/fast scan } 
      slow_sc0=true;
      slow_sc2=true;
      slow_0=slow_scan and slow_sc0;
      slow_2=slow_scan and slow_sc2;
      
      IgnoreFirstZero=true; { scan only machines, writing 1 at first step }

      dm_2=dm+dm;
      dm_2r=dm_2 -
            2*(ord(reversal)+ord(SameDir))*(1-ord(Destructive)) -
            4*ord(Destructive);
      dm_2rR=dm_2r-2*ord(reversal);
     
      dm2sqr=dm_2r*dm_2r {dm_2}; { limit size for rule finder }
      dm2qub=longint(dm2sqr)*dm_2r*2+ 1900; 
      { limit step for rule finder and size of used arrays }
      
      { 4 --> 2024, 5 --> 3000, 6 --> 4440 } 

      { t_low=0; t_mid=40000; t_hig=80000; }
      { start, midle and end tape position }

      cmax=100+dm2qub; { Upper limit for steps }
      mmax=     250; { Upper limit for used tape }  
      s_sz=     100; { Stack size }
      dum =      99; { undefined state }
      dump_max= 400; { how many dump steps }
      rmax=    3000; { Upper limit for rules }
                     { 2000 is small for some machines !!! }
      sr_lmax=   31; { max len for approved shift rules }
      showmax=   20; { How many proved machines to show from any group }
      bmax=      64; { Limit for basic rulei and exones arrays }

      { Test results: }
      e_max=21; 
      nm_end=1;  { normal finish }
      mem_ov=2;  { tape overflow } 
      too_lng=3; { time overflow } 
      { Hard tests for infinite loops: }
      b_loop=4;  { back-track test, halt state unrechable }
      i_loop=5;  { invariant states } 
      c_loop=6;  { in place circle }
      s_loop=7;  { closed sub-graph in TM graph, halt unrechable }
      m_loop=8;  { moving left or right infinite }
      lNct_l=9;  { simple linear counter with 1 repeating word }
      modf_l=10; { finite transition graph (modulo version) }
      pfin_l=11; { finite position formula - binary or similar counters }
      swpf_l=12; { swiming position test   - binary or similar counters }
      exH0_l=13; { Exones chaotick loop 0 }
      exH1_l=14; { Exones chaotick loop 1 }
      ex0f_l=15; { finite exones graph loop }
      ex1f_l=16; { finite exones + intrones graph loop }
      exS0_l=17; { Exones special loop 0 }
      exS1_l=18; { Exones special loop 1 }
      exS2_l=19; { Exones special loop 2 }
      BLfinl=20; { finite transition graph } 
      col0_e=21; { Collatz like function }

      spec_max=10; { spectrum limit }
      

type t_arr=array[1..dm_2] of byte;
     machine=record A,B,C:t_arr end;
     TDescr = record { full state of the machine }
      { v:byte;} { value under the head }
      md:byte; { move direction }
              { only 1 of v/md must be used ! }
      s:byte; { current state }
      l,r:string; { left and right parts of the tape }
      c:longint; { step counter }
      p:longint; { tape position }
      af:boolean; { false/true - full_state/formula }
      d_c,d_p: string[40]; { delta c/p for formulas }
      {l_mark,r_mark:string[40];} { mark strings for exone proofs }
      rn:longint; { rule number }
      rname, rname0, rname1:string[4]; { rule names }
      smax:byte;
     end; 
     THistory = array[0..cmax] of TDescr;
     TRule = record { description for a shift rule }
      { syntax: *aS>b(c0)* --> *(c1)aS>b* }
      {         *(c0)b<Sa* --> *b<Sa(c1)* }
      id:word;
      md:byte; { move direction }
      s:byte;  { state }
      a{,b},c0,c1:string; { rule patterns }
      c:longint; { step needed }
      p:longint; { position moves }
      used:boolean;
      allowed:boolean;
      spectrum:array[1..spec_max] of longint;
     end;
     TRuleArr = array[0..rmax] of TRule;
     TBRuleEl = record
      c0,c1:string; { patterns }
      c:longint; { steps needed }
      ucnt:longint; { usage counter }
     end;
     TBRule = record
      id:word;
      md:byte; { move direction }
      s:byte;  { state }
      a:string; { lead rule pattern }
      Patts:array[0..bmax] of TBRuleEl;
      Patt_cnt:longint;
      ucnt:longint; { usage counter }
      nice:longint;
      m_id:longint; { main pattern index }
     end;
     TBRuleArr = array[0..bmax] of TBRule;

var Stack:array[0..s_sz] of machine;
    s_ct:0..s_sz;

    SH:THistory; { History for rule finding }
    SH_cnt:longint;
    MH:THistory; { Macro History }
    MH_cnt:longint;
    BH:THistory; { Basic Macro History }
    BH_cnt:longint;
    MMH:THistory; { Main Macro History }
    MMH_cnt:longint;
    BMH:THistory; { Bin_Macro History }
    BMH_cnt:longint;
    EMH:THistory; { Exone macro history }
    EMH_cnt:longint;
    ClMH:THistory; { Collatz macro history }
    ClMH_cnt:longint;
    
    SRules:TRuleArr;  { Approved shift rules }
    SR_cnt:longint;
    SSRules:TRuleArr;  { Special approved shift rules }
    SSR_cnt:longint;
    ASRules:TRuleArr; { All shift rules }
    ASR_cnt:longint;
    BSRules:TBRuleArr; { Basic shift rules }
    BSR_cnt:longint;
    OSRules:TRuleArr; { Opposite shift rules (to MainRule) }
    OSR_cnt, OSR_main:longint;

    ms_cnt:longint;
    
    A,B,C:t_arr; { Current machine }
    CD:TDescr; { Current full description }
    CM:TDescr; { Current macro description }
    CB:TDescr; { Current basic macro description }
    CMM:TDescr;{ Current main macro }
    BMM:TDescr;{ Current bin_macro }
    CEM:TDescr;{ Current exone macro }
    Cl_M:TDescr;{ Current Collatz macro }

    m,         { Machine counter } 
    sigma, 
    old_sec:longint;
    t_record, s_record: longint;
    e_state:byte;
    e_cnt:array[1..e_max] of longint;
    sh_ct1, sh_ct2:byte;

    a1:byte;  { position of Halt state }
    tnr,tnr1,trc,ttm,tproof,tsrec:text; 
    { files for nonregular/record/other/proved machines }

var
 rec_cnt:longint; RevS:string;
 
function SD_str(s,md:byte):string;
 begin
  if md=0
   then SD_str:='<'+chr(s+ord('@'))
   else SD_str:=chr(s+ord('@'))+'>';
 end;

function RevStr(s:string):string;
 var w:string; i,n:byte;
 function RevCh(c:char):char;
  begin
   case c of
    '[':c:=']';
    ']':c:='[';
    '{':c:='}';
    '}':c:='{';
    '(':c:=')';
    ')':c:='(';
   end; 
   RevCh:=c;
  end;
 begin
  w[0]:=s[0];
  n:=ord(s[0]);
  for i:=1 to n do w[i]:=RevCh(s[n-i+1]);
  RevStr:=w;
 end; 

function TD_str(var D:TDescr):string;
 begin with D do TD_str:=RevStr(l)+SD_str(s,md)+r end;
 
{ -------------------------------------------------- }

type
 TPosStat = array[0..1,1..dm] of longint;
 TPSCnt   = array[-mmax..mmax] of longint;
var 
 PosStat : array[-mmax..mmax] of TPosStat;
 PosSCnt : TPSCnt;
 pst_min, pst_max:longint;
 PosAl,PosBl,PosAr,PosBr:longint;

procedure ClPosStat;
 var i,j,k:longint;
 begin
  for i:=-mmax to mmax do begin
   PosSCnt[i]:=0;
   for j:=0 to 1 do
    for k:=1 to dm do PosStat[i][j,k]:=0;
  end;
 end;

function TuchPS(TPS1,TPS0:TPosStat):boolean;
 var s,k:longint;
 begin
  s:=0;
  for k:=1 to dm do begin
   s:=s+TPS0[1,k];
   s:=s+TPS1[0,k];
  end; 
  TuchPS:=s>0;
 end;

function cmpPos(i,j:longint):boolean;
 var OK:boolean; k:longint;
 function NotSame(m,n:longint):boolean;
  begin NotSame:=(m*n=0) and (m+n>0) end;
 begin
  OK:=true;
  for k:=1 to dm do begin
   if NotSame(PosStat[i][1,k],PosStat[j][1,k]) then OK:=false;
   if NotSame(PosStat[i-1][0,k],PosStat[j-1][0,k]) then OK:=false;
  end;
  cmpPos:=OK;
 end;

procedure EvalPosAB(var a,b:longint; sign:longint);
 var 
  i,j,lim,k,k0,j0,jm:longint;
  ta:array[byte] of boolean;
 begin
  a:=-1; k0:=-1; i:=1; 
  if sign=1 then lim:=pst_max else lim:=-pst_min;
  while i<=lim div 2 do begin
   for j:=0 to 255 do ta[j]:=false;
   for j:=1 to lim do ta[j]:=cmpPos(j*sign,(j+i)*sign);
   for j:=1 to lim-i do {if (PosSCnt[j*sign]<=3) then} begin
    k:=0;
    while ta[j+k] do inc(k);
    if (k>=i) and (k+i>k0) then begin
     k0:=k+i; 
     jm:=999;
     for j0:=j+i-1 downto j do if PosSCnt[j0*sign]<=jm then begin
      jm:=PosSCnt[j0*sign]; 
      { This is not needed !!! }
      {if jm<dm-2 then} 
       begin a:=j0; b:=a+i end;
     end;
    end;
   end;
   inc(i);
  end;
 end;
 
procedure EvalPSCnt;
 var i,k:longint;
 begin
  pst_min:=mmax; pst_max:=-mmax;
  for i:=-mmax to mmax do PosSCnt[i]:=0;
  for i:=-mmax to mmax do if TuchPS(PosStat[i],PosStat[i+1]) then begin
   if i>pst_max then pst_max:=i;
   if i<pst_min then pst_min:=i;
  end;
  for i:=pst_min+1 to pst_max do for k:=1 to dm do begin
   if PosStat[i,1,k]>0 then inc(PosSCnt[i]);
   if PosStat[i-1,0,k]>0 then inc(PosSCnt[i]);
  end;
  EvalPosAB(PosAl,PosBl,-1); 
  EvalPosAB(PosAr,PosBr, 1); 
 end;

procedure WrPosStat(var f:text);
 var i,k:longint;
 begin
  { EvalPSCnt; }
  writeln(f,' ----  PosStats: ---- ');
  for i:=pst_min+1 to pst_max do begin
   write(f,i:4,'    [>');
   write(f,i,']  ');
   for k:=1 to dm do if PosStat[i][1,k]>0 then write(f,'*') else write(f,'-');
   write(f,'  [',i,'<]  ');
   for k:=1 to dm do if PosStat[i-1][0,k]>0 then write(f,'*') else write(f,'-');
   writeln(f,'  [',PosSCnt[i],']');
  end;
  writeln(f,'L_patt: ',PosAl,'  ',PosBl);
  writeln(f,'R_patt: ',PosAr,'  ',PosBr);
  writeln(f);
 end;


{ -------------------------------------------------- }

function nod(i,j:longint):longint;
 begin
  if i*j=0 
   then if i>0 then nod:=i else nod:=j
   else if i>j 
    then nod:=nod(i-j,j)
    else nod:=nod(j-i,i);
 end;

function nok(i,j:longint):longint;
 begin
  nok:=i*j div nod(i,j);
 end;

{ -------------------------------------------------- }

function get_sec:longint;
 var d,y,h,m,s,s1:word; l:longint;
 begin
  getdate(y,m,d,s1);
  l:=d;
  gettime(h,m,s,s1);
  l:=l*24+h;
  l:=l*60+m; 
  l:=l*60+s;
  get_sec:=l;
 end;

procedure table(x,y:byte);
 begin
  gotoxy(x,y  );write('.__________.');
  gotoxy(x,y+1);write('|A ----    |');
  gotoxy(x,y+2);write('|  ----    |');
  gotoxy(x,y+3);write('|B ----    |');
  gotoxy(x,y+4);write('|  ----    |');
  gotoxy(x,y+5);write('|C ----    |');
  gotoxy(x,y+6);write('|  ----    |');
  gotoxy(x,y+7);write('|c=        |');
  gotoxy(x,y+8);write('|m=        |');
  gotoxy(x,y+9);write('.__________.');
 end;

 procedure wr_mash(x,y:byte);
  procedure wr_a(a:t_arr; b:byte);
   var i:byte;
   begin for i:=b to b+dm-1 do if a[i]=dum then write('x') else write(a[i]) end;
  begin
   gotoxy(x+3,y+1); wr_a(A,1);
   gotoxy(x+3,y+2); wr_a(A,dm+1);
   gotoxy(x+3,y+3); wr_a(B,1);
   gotoxy(x+3,y+4); wr_a(B,dm+1);
   gotoxy(x+3,y+5); wr_a(C,1);
   gotoxy(x+3,y+6); wr_a(C,dm+1);
  end;

procedure push(w:char);
 begin
  Stack[s_ct].A:=A; Stack[s_ct].B:=B; Stack[s_ct].C:=C;
  { gotoxy(s_ct+1,24); write(w); } 
  inc(s_ct);
 end;

procedure pull;
 begin
  dec(s_ct); 
  { gotoxy(s_ct+1,24); write(' '); }
  A:=Stack[s_ct].A; B:=Stack[s_ct].B; C:=Stack[s_ct].C;
 end;

procedure init_0;
 var l:longint;
 begin
  table(14, 1); table(26, 1); table(38, 1); sh_ct1:=14;
  table(14,12); table(26,12); table(38,12); sh_ct2:=14;
  m:=0; t_record:=0; s_record:=0;
  gotoxy(1,1);
  writeln('M=000000000');
  writeln('nrm='); writeln('mov=');
  writeln('tov='); writeln('b_t=');
  writeln('i_t='); writeln('c_l=');
  writeln('s_l='); writeln('m_l=');
  writeln('lNc='); 
  writeln('gMl=');
  writeln('p_l='); writeln('pSl='); 
  { writeln('brl='); writeln('bil='); }
  writeln('eH0='); writeln('eH1='); 
  writeln('e0l='); writeln('e1l='); 
  writeln('eS0='); writeln('eS1='); 
  writeln('eS2='); 
  writeln('B-L='); 
  writeln('cl0='); 
  for l:=1 to e_max do e_cnt[l]:=0;
 end;

procedure SetTM(s:string);
 var i,j:byte;
 procedure Set0(i,j:byte);
  begin
   if s[j]='H' 
    then A[i]:=0
    else A[i]:=ord(s[j])-ord('@');
   if s[j+2]='L' 
    then B[i]:=0 else B[i]:=1;
   if s[j+1]='0'
    then C[i]:=0 else C[i]:=1; 
  end;
 begin
  for i:=1 to dm do begin
   j:=(i-1)*9;
   Set0(i,j+1);
   Set0(dm+i,j+5);
  end;
 end;

procedure init_t(a1:byte);
 const x0=52; x1=x0+1;
 var l:longint;
 begin
  for l:=1 to dm_2 do begin 
   A[l]:=dum; 
   B[l]:=dum; 
   if reversal 
    then if l<=dm then C[l]:=1 else C[l]:=0
    else C[l]:=dum 
  end;
  B[1]:=0;
  if SameDir then B[1+dm]:=0;
  if IgnoreFirstZero then C[1]:=1;
  if a1=dm then begin 
   A[2]:=0; 
   if not SameDir then B[2]:=0; 
   C[2]:=1 
  end else begin 
   A[a1]:=0; 
   if not SameDir then B[a1]:=0; 
   if not reversal then C[a1]:=1 
  end;
  if Destructive then begin
   if reversal or SameDir then begin
    writeln;
    writeln('Reversal and SameDir must be false !!!');
    Halt;
   end;
   for l:=1 to dm do C[dm+l]:=1;
  end;

  { SpecalSubClasses rev0/rev1 }
  
  { C[1]:=1; C[2]:=1; C[3]:=1; C[4]:=1;  C[5]:=1; }  
   
  { C[6]:=0; C[7]:=0; C[8]:=0; C[9]:=0; C[10]:=0; } 
   
  
  { test some special machines: }

  { PackG_0 hint --> ExCnt>4 in ManyExones check }
  {SetTM('C1L A0L  H1L F0R  D1R C0L  A1L E0R  F1R F0R  D1R B0L  | 42699 ExScan bug ');}

  { TM4 record }
{
  A[1]:=3; A[2]:=0; A[3]:=1; A[4]:=4;  
  A[5]:=3; A[6]:=4; A[7]:=2; A[8]:=1; 
  
  B[1]:=0; B[2]:=0; B[3]:=1; B[4]:=0;
  B[5]:=1; B[6]:=1; B[7]:=1; B[8]:=0;   

  C[1]:=1; C[2]:=1; C[3]:=1; C[4]:=1;  
  C[5]:=1; C[6]:=1; C[7]:=0; C[8]:=0;   
}

  { TM5 M# 572813 Sigma record for TM5 }
{
  A[1]:=3; A[2]:=0; A[3]:=4; A[4]:=1;  A[5]:=1; 
  A[6]:=1; A[7]:=4; A[8]:=3; A[9]:=5; A[10]:=2;
  
  B[1]:=0; B[2]:=0; B[3]:=1; B[4]:=0;  B[5]:=0;
  B[6]:=0; B[7]:=1; B[8]:=1; B[9]:=1; B[10]:=1;  

  C[1]:=1; C[2]:=1; C[3]:=1; C[4]:=1;  C[5]:=1;
  C[6]:=1; C[7]:=0; C[8]:=1; C[9]:=1; C[10]:=1;  
}

  { TM5 M# 2001667 (dm+1) CollatzLoop gfin_max=1303 }
{
  A[1]:=2; A[2]:=3; A[3]:=4; A[4]:=1;  A[5]:=4; 
  A[6]:=0; A[7]:=5; A[8]:=3; A[9]:=5; A[10]:=2;
  
  B[1]:=0; B[2]:=1; B[3]:=1; B[4]:=1;  B[5]:=1;
  B[6]:=0; B[7]:=0; B[8]:=0; B[9]:=1; B[10]:=0;  

  C[1]:=1; C[2]:=1; C[3]:=0; C[4]:=0;  C[5]:=1;
  C[6]:=1; C[7]:=1; C[8]:=1; C[9]:=1; C[10]:=0;  
}

  { TM5 M# 5054949 (dm+1) - hint_1 }
{
  A[1]:=2; A[2]:=3; A[3]:=4; A[4]:=4;  A[5]:=1; 
  A[6]:=0; A[7]:=5; A[8]:=3; A[9]:=2; A[10]:=5;
  
  B[1]:=0; B[2]:=1; B[3]:=1; B[4]:=0;  B[5]:=0;
  B[6]:=0; B[7]:=0; B[8]:=1; B[9]:=0; B[10]:=1;  

  C[1]:=1; C[2]:=1; C[3]:=0; C[4]:=1;  C[5]:=1;
  C[6]:=1; C[7]:=1; C[8]:=0; C[9]:=0; C[10]:=0;  
}

  { TryBL_Loop examples: }
  { TM5 M# 408483 (dm+1) m_cnt must be at least 4 ! }
{
  A[1]:=2; A[2]:=3; A[3]:=4; A[4]:=2;  A[5]:=1; 
  A[6]:=0; A[7]:=2; A[8]:=4; A[9]:=5; A[10]:=3;
  
  B[1]:=0; B[2]:=1; B[3]:=0; B[4]:=0;  B[5]:=1;
  B[6]:=0; B[7]:=0; B[8]:=1; B[9]:=1; B[10]:=1;  

  C[1]:=1; C[2]:=1; C[3]:=1; C[4]:=1;  C[5]:=1;
  C[6]:=1; C[7]:=0; C[8]:=1; C[9]:=1; C[10]:=0;
}
 
  { TM5 M# 5167582 (dm+1) TIntroneSet.strlen must be ~ 40 ! }
{
  A[1]:=2; A[2]:=3; A[3]:=4; A[4]:=1;  A[5]:=2; 
  A[6]:=0; A[7]:=5; A[8]:=3; A[9]:=5; A[10]:=3;
  
  B[1]:=0; B[2]:=1; B[3]:=1; B[4]:=1;  B[5]:=1;
  B[6]:=0; B[7]:=0; B[8]:=0; B[9]:=1; B[10]:=0;  

  C[1]:=1; C[2]:=1; C[3]:=1; C[4]:=1;  C[5]:=1;
  C[6]:=1; C[7]:=1; C[8]:=0; C[9]:=0; C[10]:=1;  
}

  { -------------------- }
  
  { TM5 M# 1602350 (dm+2) solved for rmax=3000 !!! }
{
  A[1]:=3; A[2]:=1; A[3]:=4; A[4]:=5;  A[5]:=1; 
  A[6]:=4; A[7]:=0; A[8]:=2; A[9]:=4; A[10]:=4;
  
  B[1]:=0; B[2]:=0; B[3]:=1; B[4]:=1;  B[5]:=1;
  B[6]:=0; B[7]:=0; B[8]:=0; B[9]:=1; B[10]:=1;  

  C[1]:=1; C[2]:=0; C[3]:=1; C[4]:=0;  C[5]:=1;
  C[6]:=0; C[7]:=1; C[8]:=0; C[9]:=1; C[10]:=0;  
}
  
  { TM5 M# 5504459 (dm+2) solved for cmax=4000 !!! }
{
  A[1]:=3; A[2]:=4; A[3]:=4; A[4]:=1;  A[5]:=2; 
  A[6]:=5; A[7]:=0; A[8]:=1; A[9]:=5; A[10]:=3;
  
  B[1]:=0; B[2]:=0; B[3]:=1; B[4]:=0;  B[5]:=0;
  B[6]:=0; B[7]:=0; B[8]:=1; B[9]:=1; B[10]:=1;  

  C[1]:=1; C[2]:=0; C[3]:=1; C[4]:=1;  C[5]:=1;
  C[6]:=0; C[7]:=1; C[8]:=1; C[9]:=0; C[10]:=0;  
}

  { --------- Last proved -------- }

  { dm_0 }
  {
  SetTM('C1L A1R  H1L C1R  D1L E1L  B1R D1R  A0R C0L  | 10224040 | SRec |  20 |  0  4  0  8  0  6');
  SetTM('C1L E1R  H1L E0L  D1L C0L  A1R B1R  D1R A0R  | 10974233 | ---- | 316 |  0  7  5 10  0 17');
  SetTM('C1L E1R  H1L C1L  D1L C0L  A1R B0R  D1R A0R  | 10979960 | ---- | 325 |  0  6  5  9  0 16');
  SetTM('C1L E0R  H1L D0R  D1L A0L  A1R A1L  B1R D1R  | 11554135 | ---- | 654 |  0  0  4  6  2  0');
  SetTM('C1L E1R  H1L A1L  D0R D0L  B1L D1R  A1L A0R  | 21992948 | ---- |1340 |  0  0  3 13  0  5');
  SetTM('C1L E1R  H1L A1L  D0R D0L  B1L D1R  A0R A0R  | 21993025 | ---- |1312 |  0  0  3 13  0  5');
  SetTM('C1L E1R  H1L A1L  D0R D0L  B1L D1R  A0R A0L  | 21993204 | ---- |1625 |  0  0  3 13  0  5');
  SetTM('C1L D1R  H1L E1L  D0R C0L  E1R A1R  A1L B1L  | 22976011 | ---- |  32 |  0  5  4  0  4  9');
  }

  { dm_2 }
  {
  SetTM('C1L C0R  D0L H1L  D1R E0L  C1L E0R  A1R B1L  |  5585454 | ---- |3000 |  0  0  0 10  0 20');
  SetTM('C1L D0R  A0L H1L  A1R D0L  E1R B1L  C1L C0R  | 23741566 | ---- |3000 |  0  0  0 10  0 20');
  SetTM('C1L E0L  A1R H1L  D0R E1L  D1R B1R  C0R A0L  | 28775330 | SRec |  37 |  0  3  0  0  0  0');
  SetTM('C1L D1R  A1R H1L  D0R E1L  B1R D0L  C0R E0L  | 31305274 | SRec |   5 |  0  0  5  0  0  0');
  SetTM('B1L A0R  C1L H1L  D1R A1L  A0L E1R  D0L E0R  | 47443779 | SRec |   5 |  0  0  5  0  0  0');
  }

  { STM_6 }
  {
  SetTM('C1L D0L  H1L F0L  D1R F0R  E1R C0R  F1R D0R  B1L A0L  |    83157 | ---- | 481 |  0  7  2');
  }
  
  { --------- Not proved --------- }

  { STM_6 }
  {
  }
  
  { dm_0 }
  {
  SetTM('C1L E1L  H1L D1L  D1R D0L  A1L E1R  B0L C0R  |   827123 | HH-- |3000 |  0  2  6  5 10 13');
  SetTM('C1L E0R  H1L C0R  D1R A0L  A1R D1R  A1L B0R  |  1668912 | H--- |3000 |  0  3  0 14  0  4');
  SetTM('C1L A0R  H1L E1L  D1R B0L  A1R C1R  C0L D1L  |  2523420 | ---- |1946 |  0 40  0 44  6 50');
  SetTM('C1L D0R  H1L E0L  D1R C1L  E1L A1R  B1L D0L  |  3911891 | H--- |1942 |  0  9  0  8  0 22');
  SetTM('C1L B0R  H1L C0R  D1L C0L  E0R C1L  A0R E1R  | 11997798 | ---- |3000 |  2  4  8  8 14 30');
  SetTM('C1L D0R  H1L E1L  C1R A1R  E0L D1R  B1L C1L  | 14788712 | SRec |  10 |  0  3  0  0  0  0');
  SetTM('C1L D1R  H1L C0L  A1R C1L  E1R A0R  B1L E0L  | 18119527 | H--- |  39 |  0  6  0  0  0  0');
  SetTM('C1L C0L  H1L D1R  D0R C1L  B1R E1R  E1L A1L  | 21155496 | SRec |   3 |  0  3  0  0  0  0');
  SetTM('C1L B1L  H1L E0L  D0R C0L  A1R D1R  A0R B0L  | 22046343 | SRec |   4 |  2  4  0  0  0  0'); 
  SetTM('C1L E0L  H1L E1L  D0R A1L  A0L C1R  C1R B0L  | 22600133 | H--- |3000 |  0  7  4  6 10  0');
  }

  { dm_1 }
  {
  SetTM('B1L H1L  C0R C0L  E1L D0R  C1R D1R  B1R A0L  | 12689995 | BL_1 |2759 |  0  0  4  6  0  0');
  }
  { 
  SetTM('B1L H1L  C1R E0R  D1L B0R  D0L A1L  C0R A0L  |  5359517 | ---- |3000 |  0  6 10 14 17 21');
  SetTM('B1L H1L  C1L B1R  D1R E1L  B1R D0R  A1L C0L  |  6594274 | ---- | 337 |  0  6  0 14  0  7');
  SetTM('B1L H1L  C0R D1L  D1R C1R  E1L E0L  A0L B0R  | 11530505 | ---- |3000 |  2  0  0 11  3  3');
  SetTM('B1L H1L  C0R E1L  D0R C1R  A1L B1R  B0L A0L  | 11679832 | ---- |1012 |  0  0  0  7 12  0');
  SetTM('B1L H1L  C0R C1R  D1R B1R  E1L D1L  A0R E0L  | 11934239 | SRec |  15 |  0  4  0  0  0  0');
  SetTM('B1L H1L  C0L C1R  D1L C1L  E1R D1R  A0L E0R  | 14521014 | SRec |   3 |  3  0  0  0  0  0');
  SetTM('B1L H1L  C0L C1L  D1L C1L  E1R D1R  A0L E0R  | 14521098 | SRec |   3 |  3  0  0  0  0  0');
  SetTM('B1L H1L  C0L C1L  D1L B1L  E1R D1R  A0L E0R  | 14521100 | SRec |   4 |  0  4  0  0  0  0');
  SetTM('B1L H1L  C0L B1R  D1L C1L  E1R D1R  A0L E0R  | 14521240 | SRec |   4 |  4  0  0  0  0  0');
  SetTM('B1L H1L  C0L B0L  C1R D0R  A1L E0R  A0R E0R  | 15076017 | ---- |2349 |  2  2  3  9  0  0');
  }

  { dm_2 }
  {
  SetTM('C1L E1L  E1R H1L  D1R C1R  B0L D0R  A0L A1L  |  7119815 | SRec |  13 |  0  4  0  0  0  0');
  SetTM('C1L E1R  D1R H1L  D1L C0L  A1R D1L  B1R A0R  | 12568936 | ---- | 319 |  0  6  0 14  0  7');
  SetTM('C1L B0R  E0R H1L  D0L C1L  E1L C0L  A1R C0R  | 33424333 | ---- |3000 |  2  5  9  7 20 29');
  SetTM('C1L D1R  E1R H1L  D0L C0L  B1R A0R  A1R E1L  | 34364505 | ---- | 481 |  0  6  0 10  0  0');
  SetTM('B1L D1L  C1R H1L  E1R D1R  E1L C0R  A1L D0L  | 43710027 | ---- |3000 |  0  4  4  0  0 20');
  SetTM('B1L A0L  C1R H1L  C0R D0R  E1L B0L  E0L A1L  | 45963385 | ---- |3000 |  3  0  2  0  2  2');
  SetTM('B1L A0R  C0L H1L  C1R D1L  E1L A1R  B0L D0R  | 54769539 | ---- |3000 |  4  6  0  0 18 12');

  Type _3N_:
  SetTM('C1L D0L  A1L H1L  D1R E0R  B0R C0R  C1R B0L  |  7915298 | ---- | 112 |  0  6  0  0  0  0');
  SetTM('C1L B0R  E1R H1L  D1L A0L  B0L C0L  C1R D0R  | 14934318 | ---- | 158 |  0  6  0  0  0  0');
  SetTM('C1L E0L  D1R H1L  B0L A0L  A1R C0R  A1L B0R  | 39779768 | ---- |  99 |  0  6  0  0  0  0');
  }


  { ----- Not solved examples: -------- }
  
  { TM5 M# 8450515 (dm+2) TryBL_Loop hint }
  {C1L A1L  E1R H1L  D1R A0L  E1L B0R  C0L C0R   id  8450515}
{
  A[1]:=3; A[2]:=5; A[3]:=4; A[4]:=5;  A[5]:=3; 
  A[6]:=1; A[7]:=0; A[8]:=1; A[9]:=2; A[10]:=3;
  
  B[1]:=0; B[2]:=1; B[3]:=1; B[4]:=0;  B[5]:=0;
  B[6]:=0; B[7]:=0; B[8]:=0; B[9]:=1; B[10]:=1;  

  C[1]:=1; C[2]:=1; C[3]:=1; C[4]:=1;  C[5]:=0;
  C[6]:=1; C[7]:=1; C[8]:=0; C[9]:=0; C[10]:=0;  
}

  {C1L E0L  A1R H1L  D1R A0L  D0R B1R  C0L B0R   id  3198755  dm_2 }
{
  A[1]:=3; A[2]:=1; A[3]:=4; A[4]:=4;  A[5]:=3; 
  A[6]:=5; A[7]:=0; A[8]:=1; A[9]:=2; A[10]:=2;
  
  B[1]:=0; B[2]:=1; B[3]:=1; B[4]:=1;  B[5]:=0;
  B[6]:=0; B[7]:=0; B[8]:=0; B[9]:=1; B[10]:=1;  

  C[1]:=1; C[2]:=1; C[3]:=1; C[4]:=0;  C[5]:=0;
  C[6]:=0; C[7]:=1; C[8]:=0; C[9]:=1; C[10]:=0;  
}

  
  { TM5 M# 827123 BL_Mod ??? }
{
  A[1]:=3; A[2]:=0; A[3]:=4; A[4]:=1;  A[5]:=2; 
  A[6]:=5; A[7]:=4; A[8]:=4; A[9]:=5; A[10]:=3;

  B[1]:=0; B[2]:=0; B[3]:=1; B[4]:=0;  B[5]:=0;
  B[6]:=0; B[7]:=0; B[8]:=0; B[9]:=1; B[10]:=1;  

  C[1]:=1; C[2]:=1; C[3]:=1; C[4]:=1;  C[5]:=0;
  C[6]:=1; C[7]:=1; C[8]:=0; C[9]:=1; C[10]:=0;  
}

  { TM5 M# 1668912 mod 12/16 ??? }
{
  A[1]:=3; A[2]:=0; A[3]:=4; A[4]:=1;  A[5]:=1; 
  A[6]:=5; A[7]:=3; A[8]:=1; A[9]:=4; A[10]:=2;

  B[1]:=0; B[2]:=0; B[3]:=1; B[4]:=1;  B[5]:=0;
  B[6]:=1; B[7]:=1; B[8]:=0; B[9]:=1; B[10]:=1;  

  C[1]:=1; C[2]:=1; C[3]:=1; C[4]:=1;  C[5]:=1;
  C[6]:=0; C[7]:=0; C[8]:=0; C[9]:=1; C[10]:=0;  
}

  { TM5 M# 2523420 BL_mod ???  }
{
  A[1]:=3; A[2]:=0; A[3]:=4; A[4]:=1;  A[5]:=3; 
  A[6]:=1; A[7]:=5; A[8]:=2; A[9]:=3; A[10]:=4;

  B[1]:=0; B[2]:=0; B[3]:=1; B[4]:=1;  B[5]:=0;
  B[6]:=1; B[7]:=0; B[8]:=0; B[9]:=1; B[10]:=0;  

  C[1]:=1; C[2]:=1; C[3]:=1; C[4]:=1;  C[5]:=0;
  C[6]:=0; C[7]:=1; C[8]:=0; C[9]:=1; C[10]:=1;  
}

  { TM5 M# 3911891 BL_mod or pSl_2 ??? }
{
  A[1]:=3; A[2]:=0; A[3]:=4; A[4]:=5;  A[5]:=2; 
  A[6]:=4; A[7]:=5; A[8]:=3; A[9]:=1; A[10]:=4;

  B[1]:=0; B[2]:=0; B[3]:=1; B[4]:=0;  B[5]:=0;
  B[6]:=1; B[7]:=0; B[8]:=0; B[9]:=1; B[10]:=0;  

  C[1]:=1; C[2]:=1; C[3]:=1; C[4]:=1;  C[5]:=1;
  C[6]:=0; C[7]:=0; C[8]:=1; C[9]:=1; C[10]:=0;  
}

  { TM5 M# 51813884 x(n)y(2n)z --> u(n)x(2n)yz }
{
  A[1]:=3; A[2]:=0; A[3]:=4; A[4]:=1;  A[5]:=3; 
  A[6]:=2; A[7]:=1; A[8]:=3; A[9]:=5; A[10]:=5;

  B[1]:=0; B[2]:=0; B[3]:=1; B[4]:=0;  B[5]:=1;
  B[6]:=0; B[7]:=0; B[8]:=0; B[9]:=1; B[10]:=1;  

  C[1]:=1; C[2]:=1; C[3]:=1; C[4]:=0;  C[5]:=1;
  C[6]:=1; C[7]:=0; C[8]:=1; C[9]:=0; C[10]:=1;  
}

  { TM5 M# 6311798 ??? }
{
  A[1]:=3; A[2]:=0; A[3]:=4; A[4]:=1;  A[5]:=3; 
  A[6]:=1; A[7]:=4; A[8]:=5; A[9]:=3; A[10]:=2;

  B[1]:=0; B[2]:=0; B[3]:=1; B[4]:=0;  B[5]:=1;
  B[6]:=0; B[7]:=0; B[8]:=0; B[9]:=1; B[10]:=0;  

  C[1]:=1; C[2]:=1; C[3]:=1; C[4]:=1;  C[5]:=1;
  C[6]:=1; C[7]:=0; C[8]:=0; C[9]:=0; C[10]:=0;  
}

  { TM5 M# 123831 (dm+2) }
{
  A[1]:=3; A[2]:=1; A[3]:=4; A[4]:=2;  A[5]:=3; 
  A[6]:=5; A[7]:=0; A[8]:=5; A[9]:=5; A[10]:=1;
  
  B[1]:=0; B[2]:=0; B[3]:=1; B[4]:=1;  B[5]:=1;
  B[6]:=0; B[7]:=0; B[8]:=1; B[9]:=1; B[10]:=0;  

  C[1]:=1; C[2]:=1; C[3]:=1; C[4]:=1;  C[5]:=1;
  C[6]:=1; C[7]:=1; C[8]:=0; C[9]:=1; C[10]:=0;  
}
  
{ --------- end of not solved ---------- }
  
{ ----------- ShiftRec machines (hand proved) ------------- } 

  { TM5 M# 764350 (dm+1) bin_spec ??? }
{
  A[1]:=2; A[2]:=3; A[3]:=5; A[4]:=3;  A[5]:=4; 
  A[6]:=0; A[7]:=1; A[8]:=4; A[9]:=2; A[10]:=5;
  
  B[1]:=0; B[2]:=1; B[3]:=0; B[4]:=1;  B[5]:=1;
  B[6]:=0; B[7]:=0; B[8]:=1; B[9]:=0; B[10]:=0;  

  C[1]:=1; C[2]:=1; C[3]:=1; C[4]:=0;  C[5]:=0;
  C[6]:=1; C[7]:=0; C[8]:=1; C[9]:=0; C[10]:=0;  
}

  s_ct:=0; push('\');
  table (x0,12);  wr_mash(x0,12);
  gotoxy(x1,19); write('c=',cmax:6);
  gotoxy(x1,20); write('m=',mmax:6);
 end;

function HTSize(s:string):longint;
 begin
  HTSize:=length(s)-1;
 end;
 
procedure wr_state(var f:text; var CD:TDescr);
 var spc:longint; ws,l1,r1:string;
 procedure Ch(var l:string);
  begin
   case l[1] of
    '.':l[1]:='^';
    '-':l[1]:='=';
    '+':l[1]:='#';
   end;
  end;
 begin 
  with CD do begin
   spc:=20-md+p-HTSize(l); ws:='';
   while spc>0 do begin dec(spc); ws:=ws+' ' end;
   write(f,p:4,' ',SD_str(s,md),ws);
   l1:=l; r1:=r;
   if md=0 then Ch(l1) else Ch(r1);
   writeln(f,RevStr(l1),r1);
  end; 
 end;

procedure wr_history(var f:text);
 var i,lim:longint;
 begin
  writeln(f);
  writeln(f,'--------- Simple History: ---------');
  SH[SH_cnt]:=CD;
  lim:=SH_cnt; if lim>dump_max then lim:=dump_max;
  for i:=0 to lim do begin
   write(f,i:4,': ');
   wr_state(f,SH[i]);
  end; 
  writeln(f);
  writeln(f,'-----------------------------------');
 end;

var
 p_left,p_right:longint;
 
function MemUsed(var D:TDescr):longint;
 begin
  MemUsed:={HTSize(D.l)+HTSize(D.r)} p_right-p_left+1;
 end;
 
{ --- Making a simple step: --- }

type
 bitchar=array[0..1] of char;
const
 V_str:bitchar=('-','+');

function GetDV(var D:TDescr):byte;
 function V(l:string):byte;
  begin 
   if l='.' then V:=0 else if l[1]='-' then V:=0 else V:=1
  end;  
 begin
  if D.md=0 then GetDV:=V(D.l) else GetDV:=V(D.r) 
 end;
 
procedure Expand(var s:string; n:byte);
 begin if s[length(s)]='.' then begin
  s[length(s)]:='-';
  while length(s)<n do s:=s+'-'; 
 end end;
function GetF(s:string; n1,n2:longint):string;
 var w:string;
 begin if n2=0 then GetF:='' else begin
  w:=copy(s,n1,n2); if w='' then w:='.';
  Expand(w,n2); GetF:=w;
 end end;
function MSign(s:string):boolean;
 var n:byte;
 begin
  MSign:=true;
  for n:=1 to length(s) do if s[n]<>'-' then MSign:=false;
 end;

{ -------------- Proof utilities ---------- }

const
 EL_base={ord('a')} 128+64;
 EL_leter=ord('a');
 E_leters=[chr(EL_base)..chr(EL_base+63)];

const
 digits=['0'..'9'];
 leters=['a'..'z'];

var
 pr_fail:boolean;
 fin_att:longint;
 
{ --------- AF primitives ------------ }
{ AF = int | var | var+int | var-int   }
{ var = small_leter ('u' - for error ) }

procedure AF_dec(var s:string; n:longint);
 var m,i:longint; v,sign:char; ws:string;
 procedure make(n:longint);
  begin
   Str(n,ws);
   if n>0 then s:=v+'+'+ws
   else if n=0 then s:=v
   else s:=v+ws;
  end;
 begin if s<>'u' then begin
  v:=s[1];
  if v in digits then begin
   val(s,m,i);
   if m-n<0 then s:='u' else Str(m-n,s);
  end else begin
   delete(s,1,1);
   if s<>'' then begin
    sign:=s[1]; delete(s,1,1);
    val(s,m,i);
    case sign of
     '-':make(0-m-n);
     '+':make(m-n)
    end;
   end else make(0-n)
  end;
 end end;

procedure AF_inc(var s:string; n:longint);
 begin AF_dec(s,-n) end;

function AF_add(s1,s2:string):string;
 var s,w:string;
 procedure Add(f,sn:string);
  var m,i:longint;
  begin
   s:=f;
   val(sn,m,i);
   AF_inc(s,m);
  end;
 begin
  if s2[1] in digits then Add(s1,s2)
  else if s1[1] in digits then Add(s2,s1)
  else if (s1[1]='x') and (s2[1]='x') 
   then begin { x is special var for modulo arithmetick !!! }
    w:=s2; delete(w,1,2);
    Add(s1,w);
   end else s:='u';
  AF_add:=s;
 end;

function AF_make_mod(s:string; modulo:longint):string;
 var m,i:longint; w:string;
 begin
  val(s,m,i);
  m:=m mod modulo;
  if m=0 then m:=modulo;
  Str(m,w);
  AF_make_mod:='x+'+w;
 end;

function AF_adjust_mod(var s:string; modulo:longint):boolean;
 var m,i:longint; w:string;
 begin
  if s='x' then begin
   AF_adjust_mod:=true;
   Str(modulo,w);
   s:='x+'+w;
  end else begin
   AF_adjust_mod:=false;
   w:=s; delete(w,1,2);
   val(w,m,i);
   m:=m mod modulo;
   if m=0 then m:=modulo;
   Str(m,w);
   s:='x+'+w;
  end; 
 end;

{ ----------------------------------- }

procedure UnpackFirst(var l:string);
 var pat,cnt:string; x,y:longint; 
 begin if l[1]='(' then begin
  x:=Pos('|',l);
  pat:=copy(l,2,x-2);
  y:=Pos(')',l);
  cnt:=copy(l,x+1,y-x-1);
  if cnt='1'
   then l:=pat+copy(l,y+1,length(l)-y)
   else begin
    AF_dec(cnt,1);
    l:=pat+'('+pat+'|'+cnt+')'+copy(l,y+1,length(l)-y) 
   end;
 end end;

function TestForPatt(c1,l:string):byte;
 begin
  TestForPatt:=0;
  if c1=GetF(l,1,length(c1))
   then TestForPatt:=1 
   else if l[1]='(' 
    then if c1=copy(l,2,Pos('|',l)-2) 
     then TestForPatt:=2;
 end;

function TestForROLPatt(c1:string; var l:string):byte;
 var n:byte; h,c2,l1,cnt:string;
 begin
  TestForROLPatt:=0;
  if c1=GetF(l,1,length(c1))
   then TestForROLPatt:=1 
   else if l[1]='(' then begin 
    if c1=copy(l,2,Pos('|',l)-2) 
     then TestForROLPatt:=2;
   end else begin
    n:=Pos('(',l);
    if (n>1) and (n-1<length(c1)) then begin
     h:=copy(l,1,n-1);
     l1:=l; delete(l1,1,n-1);
     c2:=copy(l1,2,Pos('|',l1)-2);
     if c1+h=h+c2 then begin
      TestForRolPatt:=3;
      delete(l1,1,Pos('|',l1)-1);
      cnt:=copy(l1,1,Pos(')',l1));
      delete(l1,1,Pos(')',l1));
      l:='('+c1+cnt+h+l1;
     end;
    end;
   end;
 end;

procedure incS(a:string; var s:string; af:boolean);
 begin
  if length(a)+length(s)>mmax then 
   if af then pr_fail:=true else e_state:=mem_ov;
  s:=a+s;
  while (length(s)>1) and (s[length(s)-1]='-') 
   do delete(s,length(s)-1,1);
 end;

function EatPatt(var c1,l:string; kill:boolean):string;
 var pat,cnt,old:string; n,x,y:longint; endt:boolean;
 begin
  n:=0; old:=l; cnt:='0';
  case TestForROLPatt(c1,l) of
   1:begin
      endt:=false;
      repeat
       delete(l,1,length(c1)); 
       if l='' then begin
         l:='.';
         endt:=MSign(c1); 
       end;  
       inc(n);
       pat:=GetF(l,1,length(c1));
      until (pat<>c1) or endt; 
      if kill and endt then e_state:=m_loop;
      Str(n,cnt);
     end;
   2,3:begin
      x:=Pos('|',l);
      y:=Pos(')',l);
      cnt:=copy(l,x+1,y-x-1);
      l:=copy(l,y+1,length(l)-y);
     end;
  end; 
  if old=l 
   then EatPatt:=cnt
   else EatPatt:=AF_add(cnt,EatPatt(c1,l,kill));
 end;

var 
 rep_min,rule_min:longint;

procedure IncPatt(var c,l,cnt:string; af:boolean; n:byte);
 var i,j:longint;
 begin
  if cnt[1] in digits 
   then Val(cnt,i,j) else i:=999;
  if i<=rep_min+n 
   then for j:=1 to i do incS(c,l,af)
   else incS('('+c+'|'+cnt+')',l,af);
 end;

function ShiftPatt(var r,c0,l,c1:string; af:boolean):string;
 var cnt,n,m:string; 
 begin
  n:=EatPatt(c0,r,true);
  m:=EatPatt(c1,l,false);
  cnt:=AF_add(n,m);
  IncPatt(c1,l,cnt,af,0);
  ShiftPatt:=n;
 end;

{
 There is something wrong with procedure PackPatt.
 After i apply it, the tov increased by 124 for RTM(5)
 The following tests decreased:
 c_l with 32, m_l with 48, lNc with 44. 
 After some improvements this is corrected, but this
 mechanism seems to be ensure.
}

const IP_rec:byte=0;
type 
 TIRule = record
  s,md:byte;
  l,r,h:string;
 end;
var
 IPArr: array[byte] of TIRule;
 IP_cnt:byte;

function SimStr(s1,s2:string):boolean; forward;

procedure PackPatt(var l,r:string; af:boolean; s,md:byte);
 var n,i,k:longint; h,h1,t,t1,cnt:string; succ:boolean; n1:byte;
 function IPexist:boolean; 
  var i:byte; 
  begin
   IPexist:=false;
   if IP_cnt>0 then for i:=0 to IP_cnt-1 do
    if (IPArr[i].l=t1) and (IPArr[i].h=h) and
       (IPArr[i].md=md) and (IPArr[i].s=s) and
       SimStr(r,IPArr[i].r)
     then IPexist:=true;
  end; 
 procedure Pack;
  begin
   if TestForPatt(h,t)>0 then begin
    cnt:=EatPatt(h,l,false);
    if rule_min>0
     then IncPatt(h,l,cnt,af,0)
     else IncPatt(h,l,cnt,af,9);
    succ:=true;
   end;
  end;
 procedure Pack_2;
  var succ:boolean;
  begin
   succ:=true;
   while length(h)>=length(h1) do begin
    if Pos(h1,h)<>1 then succ:=false;
    delete(h,1,length(h1));
   end;
   if succ and (h='') then begin
    cnt:=EatPatt(h1,l,false);
    if rule_min>0
     then IncPatt(h1,l,cnt,af,0)
     else IncPatt(h1,l,cnt,af,9);
   end;
  end;
 begin
  n:=Pos('(',l); succ:=false;
  if n=0 then begin
   n:=length(l);
   if n>4 then for i:=1 to (n div 3) do 
   if (rule_min=0) or (rule_min=i) then begin
    h:=copy(l,1,i); t:=l;
    delete(t,1,i);
    if (not succ) and (Pos(h,t)=1) then begin
     t1:=t; k:=1;
     while Pos(h,t1)=1 do 
      begin delete(t1,1,i); inc(k) end;
     if length(t1)>1 then begin
      n1:=length(t1)-1;
      if (Pos(copy(t1,1,n1),h)=1) and 
         MSign(copy(h,n1+1,length(h)-n1))
       then begin inc(k); t1:='.' end;
     end;
                  { PackPatt tuning }  
     if (k>dm) or ((k>1) and (rule_min>0)) then begin
      if (not IPexist) and (IP_cnt<255) then begin 
       IPArr[IP_cnt].l:=t1; 
       IPArr[IP_cnt].r:=r; 
       IPArr[IP_cnt].h:=h; 
       IPArr[IP_cnt].s:=s; 
       IPArr[IP_cnt].md:=md; 
       inc(IP_cnt);
       if IP_cnt>IP_rec then begin
        IP_rec:=IP_cnt;
        gotoxy(55,3); write('IP_max=',IP_rec,' ');
       end;
      end; 
      if IP_cnt<255 then Pack;
     end; 
    end; 
   end;
  end else if n>1 then begin
   h:=copy(l,1,n-1); t:=l;
   delete(t,1,n-1); t1:=t;
   h1:=copy(t,2,Pos('|',t)-2);
   Pack_2;
   (*
   delete(t1,1,Pos(')',t1));
   if (rule_min>0) { and (rule_min<>length(h1)) } then 
    if (Pos(h1,h)=1) and (length(h) mod length(h1)=0) 
     then h:=h1;
   if IPexist then Pack;
   *)
  end;
 end;
 
procedure MakeDStep(var D:TDescr; s1,v1,d1:byte; macro:byte);
 procedure MovV(var l,r:string);
  begin
   if (v1=1) or (r<>'.') then r:=V_str[v1]+r;
   if length(r)>D.smax then D.smax:=length(r);
   if l<>'.' then delete(l,1,1);
  end;
 procedure SetV(var l,r:string);
  begin
   if (l<>'.') then begin 
    l[1]:=V_str[v1]; 
    if l='-.' then l:='.' 
   end else if v1=1 then l:='+.';
   if (macro=1) and (ms_cnt>3) {and (rule_min<=dm_2)} 
    then PackPatt(l,r,D.af,D.s,D.md);
  end;  
 begin with D do begin
  if md=0 then UnpackFirst(l) else UnpackFirst(r);
  if af and (macro>0)  
   then begin
    d_c:='1'; 
    if d1=0 then d_p:='-1' else d_p:='1';
   end 
   else begin inc(c); p:=p+d1+d1-1; end;

  if (not af)  and (macro=0) and
     (p>-mmax) and (p<mmax) then inc(PosStat[p][md,s]);

  s:=s1; 
  rn:=-1;
  if d1=md 
   then if md=0 then MovV(l,r) else MovV(r,l)
   else if md=0 then SetV(l,r) else SetV(r,l);
  md:=d1;
  if smax>=mmax then if af
   then pr_fail:=true else e_state:=mem_ov;
 end end;

function VarSCnt(s:string):longint;
 var n:longint; w:string;
 begin
  n:=0; w:=s;
  while pos('|',w)>0 do begin
   inc(n); delete(w,1,pos('|',w));
  end;
  VarSCnt:=n;
 end;

function SetNextVCnt(var s:string; v:char):char;
 var w:string; n:byte; v1:char;
 begin
  v1:=v;
  n:=pos('|',s);
  if n>0 then begin
   w:=copy(s,1,Pos('|',s));
   delete(s,1,pos(')',s));
   v1:=SetNextVCnt(s,chr(ord(v)+1));
   s:=w+v+')'+s;
  end; 
  SetNextVCnt:=v1; 
 end;

procedure SetAllVCnt(var s:string; v:char);
 var w:string; n:byte;
 begin
  n:=pos('|',s);
  if n>0 then begin
   w:=copy(s,1,Pos('|',s));
   delete(s,1,pos(')',s));
   SetAllVCnt(s,v);
   s:=w+v+')'+s;
  end; 
 end;

procedure SetAllModVCnt(var s:string; m:longint);
 var w,w1:string; n:byte;
 begin
  n:=pos('|',s);
  if n>0 then begin
   w:=copy(s,1,Pos('|',s));
   delete(s,1,Pos('|',s));
   w1:=copy(s,1,pos(')',s)-1);
   delete(s,1,pos(')',s));
   SetAllModVCnt(s,m);
   s:=w+AF_make_mod(w1,m)+')'+s;
  end; 
 end;

procedure SetVCnt(var s:string; v:string);
 var w:string;
 begin
  w:=copy(s,1,Pos('|',s));
  delete(s,1,pos(')',s));
  s:=w+v+')'+s;
 end;

procedure EraseVCnt(var s:string);
 var w:string;
 begin
  w:=copy(s,1,Pos('(',s)-1);
  delete(s,1,pos(')',s));
  s:=w+s;
 end;

function GetVCnt(s:string):string;
 var w:string;
 begin
  w:=s;
  delete(w,1,pos('|',w));
  GetVCnt:=copy(w,1,pos(')',w)-1);
 end;

function SimStr(s1,s2:string):boolean;
 var k,n1,n2:longint; w1,w2:string; succ:boolean;
 begin
  succ:=true;
  k:=VarSCnt(s1);
  w1:=s1; w2:=s2;
  if k=VarSCnt(s2) then begin
   while (k>0) and succ do begin
    n1:=pos('|',w1);
    n2:=pos('|',w2);
    succ:=copy(w1,1,n1)=copy(w2,1,n2);
    delete(w1,1,pos(')',w1));
    delete(w2,1,pos(')',w2));
    dec(k);
   end;
   if succ then succ:=w1=w2;
  end else succ:=false;
  SimStr:=succ;
 end;

function VarCount(var D:TDescr):longint;
 begin
  VarCount:=VarSCnt(D.l)+VarSCnt(D.r);
 end;

function SimMacro(var D1,D2:TDescr):boolean;
 begin
  SimMacro:=
   SimStr(D1.l,D2.l) and SimStr(D1.r,D2.r)
   and (D1.s=D2.s) and (D1.md=D2.md);
 end;

function SimMacro2(var D1,D2:TDescr):boolean;
 begin
  SimMacro2:=
   (D1.l=D2.l) and (D1.r=D2.r)
   and (D1.s=D2.s) and (D1.md=D2.md);
 end;

procedure MakeMStep(var D:TDescr); forward;

const
 gfin_max=2000 
   { 1600 is good, but small for some Exone proofs for dm_1 set }
   {1350} {3000 is max} { 1350 need for Modulo proof }; 

 { gfin_max=549; }
 { 549 is good for RTM(5), 548 is small }
 
type
 TGNode = record
  checked:boolean;
  D,Dnext:TDescr;
 end; 
 TGraph = array[0..2*gfin_max] of TGNode;
var
 gfin_lim:longint;
 CTG:TGraph;
 CTG_cnt:longint;
 CTGs:TGraph;
 CTGs_cnt:longint;

procedure TryL1Cnt(var D:TDescr; maxstep:longint);
 var 
  DF0,DF1:TDescr; i:longint; succ:boolean; lf:string; 
  GTN:TGNode;
 procedure Test(l1:string);
  var l:string;
  begin
   l:=l1;
   while VarSCnt(l)>0 do begin
    lf:=GetVCnt(l);
    if ((length(lf)>1) and (lf[2]='-')) or (lf='u') then succ:=false;
    EraseVCnt(l);    
   end;
  end;
 begin
  DF0:=D; 
  with DF0 do begin
   af:=true; p:=0; c:=0;
   SetNextVCnt(l,SetNextVCnt(r,'a'));
  end;
  DF1:=DF0;
  i:=0; succ:=false; pr_fail:=false; 
  while (not succ) and (not pr_fail) and (i<=maxstep) do begin
   GTN.D:=DF1;   
   MakeMStep(DF1);
   GTN.DNext:=DF1;  
   GTN.checked:=true;
   if i<gfin_max then begin
    CTG[i]:=GTN;
    CTG_cnt:=i+1;
   end;   
   if not pr_fail then succ:=SimMacro(DF1,DF0);
   inc(i);
  end;
  if succ and (not pr_fail) then begin
   with DF1 do begin Test(l); Test(r) end;
   if succ then begin
    e_state:=lNct_l;
   end;
  end; 
 end;

procedure wr_grapf(var f:text; var CTG:TGraph; CTG_cnt:longint; all:boolean);
 var i:longint;
 function tr(l:string):string;
  var s:string; i:byte;
  begin
   s:=l;
   for i:=1 to length(s) do 
    if ord(s[i])>=EL_base then
     s[i]:=chr(ord(s[i])+EL_leter-EL_base);
   tr:=s;  
  end;
 begin
  writeln(f,'Closed transition graph proof follows:');
  if all
   then writeln(f,' ind rule     l_mark/r_mark                    LsdR')
   else writeln(f,' ind rule                      LsdR');
  for i:=0 to CTG_cnt-1 do with CTG[i] do begin
   with D do begin
    write(f,i:4,rn:5,':  ');
    { if all then write(f,l_mark:10,'/',r_mark:10,'  '); }
    write(f,RevStr(tr(l))+SD_str(s,md)+tr(r):25);
   end; 
   if checked 
    then with DNext do writeln(f,'  -->  ',RevStr(tr(l)),SD_str(s,md),tr(r))
    else writeln(f);
  end; 
 end;

procedure CollatzLoop(
 var CD:TDescr; var MH:THistory; 
 var MH_cnt:longint; lim:longint); forward;
 
procedure TryModFin(var D0:TDescr; v_max:longint);
 var DF,DF1:TDescr; i,modulo:longint; lf:string; reps:boolean;
 function ChangeCtrs(l,l1:string):boolean;
  var w,w1:string;
  begin
   if VarSCnt(l)>0  then w:=GetVCnt(l)   else w:='*';
   if VarSCnt(l1)>0 then w1:=GetVCnt(l1) else w1:='*';
   ChangeCtrs:=w<>w1;
  end;
 function ZCheck(var l:string):boolean;
  begin 
   if VarSCnt(l)>0 then begin
    lf:=GetVCnt(l);
    ZCheck:=AF_adjust_mod(lf,modulo);
    SetVCnt(l,lf);
   end else ZCheck:=false;
  end;
 procedure Form(var l:string; modul:longint);
  var lf:string;
  begin if VarSCnt(l)>0 then begin
   lf:=GetVCnt(l);
   if lf[1]<>'x' then lf:=AF_make_mod(lf,modul);
   SetVCnt(l,lf);
  end end;
 function OldVertex(var CTG:TGraph; CTG_cnt:longint):boolean;
  var j:longint; 
  begin
   OldVertex:=false;
   for j:=0 to CTG_cnt-1 do if SimMacro2(DF,CTG[j].D)
    then OldVertex:=true;
  end;
 procedure AddVertex(var CTG:TGraph; var CTG_cnt:longint);
  begin
   if not OldVertex(CTG,CTG_cnt) then if CTG_cnt<gfin_max then begin
    CTG[CTG_cnt].D:=DF;
    CTG[CTG_cnt].checked:=false;
    inc(CTG_cnt);
   end else pr_fail:=true;
  end;
 procedure MakeModStep(var DF:TDescr; modul:longint);
  begin
   MakeMStep(DF);
   Form(DF.l,modul); Form(DF.r,modul);
   if VarCount(DF)>v_max then pr_fail:=true;
  end;
 procedure EvalModulo;
  function EvalDiff(s1,s2:string; m:longint):longint;
   var c1,c2,w1,w2:string; m1,m2,i:longint;
   begin
    if VarSCnt(s1)=0 
     then EvalDiff:=m
     else begin
      c1:=GetVCnt(s1);
      c2:=GetVCnt(s2);
      w1:=s1; w2:=s2;
      delete(w1,1,Pos(')',w1));
      delete(w2,1,Pos(')',w2));
      delete(c1,1,1); 
      delete(c2,1,1);
      if c1='' then m1:=0 else val(c1,m1,i); 
      if c2='' then m2:=0 else val(c2,m2,i);
      { writeln(ttm,'m1=',m1,' m2=',m2); }
      m1:=m1-m2; if m1<0 then m1:=-m1;
      { writeln(ttm,'delta=',m1,' m=',m); }
      if m1=0 then i:=m else i:=nok(m,m1);
      { writeln(ttm,'new_mod=',i); } 
      EvalDiff:=EvalDiff(w1,w2,i); 
     end;
   end;
  const i_max=200; 
  begin
   DF:=D0; 
   with DF do begin
    af:=true; p:=0; c:=0;
    SetAllModVCnt(l,1000); SetAllModVCnt(r,1000);
   end;
   
   pr_fail:=false;
   i:=0; DF1:=DF;
   repeat
    MakeModStep(DF,1000);
    inc(i);
   until (i=i_max) or SimMacro(DF,DF1) or pr_fail;
   
   if (i<i_max) and (not pr_fail) then begin
    modulo:=EvalDiff(DF.l,DF1.l,1);
    modulo:=EvalDiff(DF.r,DF1.r,modulo);
   end else modulo:=0; 
  end;
 begin
  gotoxy(55,5); write('M_m=',m,'/',v_max div 2);

  EvalModulo; 

  if modulo>0 then begin
  {
  writeln(ttm,'M=',m,' ModTry=',modulo,' rule_min=',rule_min);
  }

  DF:=D0; 
  with DF do begin
   af:=true; p:=0; c:=0;
   SetAllModVCnt(l,modulo); SetAllModVCnt(r,modulo);
  end;
  pr_fail:=false;
  CTG_cnt:=1; i:=0;
  with CTG[0] do begin D:=DF; checked:=false end;
  
  {
  writeln(ttm);
  writeln(ttm,'Original: ',TD_str(D0));
  writeln(ttm,'Formula:  ',TD_str(DF));
  writeln(ttm); flush(ttm);
  }
  
  repeat
   DF:=CTG[i].D; CTG[i].checked:=true;

   CTGs_cnt:=1; CTGs[0].D:=DF;   
   repeat
    DF1:=DF;
    MakeModStep(DF,modulo);
    reps:=OldVertex(CTGs,CTGs_cnt);
    if not reps then AddVertex(CTGs,CTGs_cnt);
   until ChangeCtrs(DF.l,DF1.l) or ChangeCtrs(DF.r,DF1.r)
         or reps
         or OldVertex(CTG,CTG_cnt)
         or pr_fail;
         
   CTG[i].DNext:=DF;
   if not pr_fail then 
    if ZCheck(DF.l) then begin
     ZCheck(DF.r);
     AddVertex(CTG,CTG_cnt); 
     EraseVCnt(DF.l); 
     AddVertex(CTG,CTG_cnt);
    end else if ZCheck(DF.r) then begin
     AddVertex(CTG,CTG_cnt); 
     EraseVCnt(DF.r); 
     AddVertex(CTG,CTG_cnt);
    end else AddVertex(CTG,CTG_cnt);
   inc(i)
  until (i=CTG_cnt) or pr_fail; 

  if pr_fail then begin
   {wr_grapf(ttm,CTG,CTG_cnt,false);}
 
   if DF.s=0 then CollatzLoop(Cl_M,ClMH,ClMH_cnt,cmax div 20);
   
  end else begin
   e_state:=modf_l;
   writeln(ttm,'M=',m,' modulo=',modulo,' r_min=',rule_min,' g_max=',CTG_cnt);
   flush(ttm);
  end;

  end;
 end;


const max_att=2;

procedure TryInfinity(var D:TDescr);
 var vc0,vc1,i:longint; succ,fail:boolean; 
     D1:TDescr; vcm:longint; 
 begin
  if (e_state=0) 
  then begin
   vc0:=VarCount(D);
   vcm:=vc0; D1:=D;
   if { true } vc0>0 then begin
    succ:=false; fail:=false; i:=MH_cnt;
    while (not succ) and (not fail) and (i>0) do begin
     dec(i); 
     vc1:=VarCount(MH[i]);
     if vc1<vc0
      then fail:=true
      else if vc1=vc0 
       then succ:=SimMacro(D,MH[i])
       else if vc1>vcm then begin vcm:=vc1; D1:=MH[i] end; 
    end;
    if succ and (not fail) then if vc0>0 then begin
     inc(fin_att);
     { a..z variables are usable }
     if (vc0<10 {27}) and (fin_att<max_att) then TryL1Cnt(D,MH_cnt-i);
      { Try to prove linear seq MH[i] ... --> D }
     if e_state=0 then begin
      if (gfin_lim>1600) or 
         ((gfin_lim>600 {1000}) and (rule_min>0))
       then begin
        if (e_state in [0,mem_ov,too_lng]) 
           and (
                ((vcm>vc0) and (fin_att<20*max_att)) or 
                { ((vcm=3)) or }
                ((vcm>=vc0) and (fin_att<2*max_att))
               ) 
           and (vcm<6{10})
           and (D.c>50)
         then begin
          {
          writeln(ttm,'---- vc0/vcm= ',vc0,'|',vcm,' fin_att=',fin_att,' delta_i=',MH_cnt-i);
          writeln(ttm,'Previous: ',TD_str(MH[i]));
          writeln(ttm,'Current:  ',TD_str(D1));
          flush(ttm);
          }
          TryModFin(D1,vcm+vcm);
         end; 
       end; 
     end; 
    end{ else e_state:=c_loop };
   end; 
  end;
 end;

function SuccBStep(var D:TDescr):boolean;
 var fail:boolean; i:longint;
 function Test(var l,r:string):boolean;
  var a0,c0a:string; j:longint; succ:boolean; 
  begin 
   succ:=false;
   with BSRules[i] do begin
    a0:=GetF(l,1,length(a));
    if a0=a then for j:=0 to Patt_cnt-1 do 
     if not succ then begin
      c0a:=GetF(r,1,length(Patts[j].c0));
      if c0a=Patts[j].c0 then begin
       succ:=true;
       inc(ucnt); inc(Patts[j].ucnt);
       D.rname:=Chr(ord('a')+id)+chr(ord('0')+j);
       delete(l,1,length(a)); 
       if l='' then l:='.';
       delete(r,1,length(c0a)); 
       if r='' then r:='.';
       if r='.' then begin
        inc(ucnt,1 {10} ); inc(Patts[j].ucnt,1 {10});
       end;
       D.c:=D.c+Patts[j].c;
       if D.md=1
        then D.p:=D.p+length(c0a)
        else D.p:=D.p-length(c0a);
       incS(Patts[j].c1,l,D.af); 
       incS(a,l,D.af); 
      end;
     end;
   end; 
   Test:=succ;
  end;
 begin
  fail:=true;
  i:=0; D.rname:='--';
  while fail and (i<BSR_cnt) do begin
   with BSRules[i] do 
   if (D.md=md) and (D.s=s) then if md=1 
     then fail:=not Test(D.l,D.r)
     else fail:=not Test(D.r,D.l);
   inc(i);
  end;
  SuccBStep:=not fail;
 end;

function SuccMStep(var D:TDescr; var SRules:TRuleArr; SR_cnt:longint):boolean;
 var fail:boolean; i,cnt,j:longint; wr,fcnt:string;
 function Test(var l,r:string):boolean;
  var a0:string; SR:TRule; rep:longint;
  procedure Mul(var s:string);
   var w:string; i:longint;
   begin
    w:=s;
    if rep>1 then for i:=1 to rep-1 do s:=s+w;
   end;
  begin 
  SR:=SRules[i];
  with SR do begin
   if rule_min>0 then begin
    rep:=rule_min div length(c0);
    p:=p*rep; c:=c*rep;
    Mul(c0); Mul(c1);
   end;
   Test:=false;
   a0:=GetF(l,1,length(a));
   if a0=a then begin
     wr:=r;
     
     if TestForROLPatt(c0,wr)>0 then begin

      SRules[i].used:=true;
      Test:=true;
      D.rn:=id;
      delete(l,1,length(a)); 
      if l='' then l:='.';
      r:=wr;
      fcnt:=ShiftPatt(r,c0,l,c1,D.af);
      if D.af then begin
       Str(p,wr); D.d_p:=wr+'*('+fcnt+')';
       Str(c,wr); D.d_c:=wr+'*('+fcnt+')';
      end else begin
       val(fcnt,cnt,j);
       if cnt>1 then inc(ms_cnt);
       D.p:=D.p+p*cnt; D.c:=D.c+c*cnt;
       if cnt<spec_max 
        then inc(SRules[i].spectrum[cnt])
        else inc(SRules[i].spectrum[spec_max]);
      end;
      incS(a,l,D.af); 
     end;
    
   end; 
  end end;
 begin
  fail:=true;
  i:=0;
  while fail and (i<SR_cnt) do begin
   with SRules[i] do 
   if (D.md=md) and (D.s=s) and
      ((rule_min=0) or (rule_min mod length(c0) = 0)) and
      allowed
   then if p>0 
     then fail:=not Test(D.l,D.r)
     else fail:=not Test(D.r,D.l);
   inc(i);
  end;
  SuccMStep:=not fail;
 end;

{----------------------------------}

procedure wr_bmhistory(var f:text; lmax:longint); forward;
procedure wr_exones(var f:text); forward;

procedure wr_mmhistory(var f:text; lmax:longint);
 var i,lim:longint; 
 begin
  MMH[MMH_cnt]:=CMM; 
  lim:=lmax;
  if lim>MMH_cnt then lim:=MMH_cnt;
  writeln(f);
  writeln(f,'First ',lmax,' main macro steps:');
  writeln(f,' ind   rules    p         c             LsdR');
  for i:=0 to lim do with MMH[i] do begin
   write(f,i:4,' ',rname0+' '+rname1:7,p:6,c:10,':  ');
   writeln(f,RevStr(l),SD_str(s,md),r);
  end; 
  writeln(f);
  if OSR_main>=0 then wr_bmhistory(f,3000);
  wr_exones(f);
 end;
 
procedure wr_bhistory(var f:text; lmax:longint);
 var i,lim:longint; rn0:string;
 begin
  BH[BH_cnt]:=CB; 
  writeln(f);
  writeln(f,'First ',lmax,' basic steps:');
  writeln(f,' ind  rule      p       c             LsdR');
  lim:=lmax;
  if lim>BH_cnt then lim:=BH_cnt;
  for i:=0 to lim do with BH[i] do begin
   if rname[1] in ['A'..'Z'] 
    then rn0:='  '+rname
    else rn0:=rname+'  ';
   write(f,i:4,'  ',rn0,p:6,c:10,':  ');
   writeln(f,RevStr(l),SD_str(s,md),r);
  end; 
  writeln(f);
  for i:=1 to BH_cnt do
  if BH[i].rname[1] in ['a'..'z'] then begin
   if BH[i-1].rname[1] in ['A'..'Z'] then writeln(f);
   write(f,BH[i].rname);   
  end;
  writeln(f);
 end;
 
procedure wr_macro_history(
 var f:text; 
 var CM:TDescr; var MH:THistory; MH_cnt:longint;
 lmax:longint);
 var i,lim:longint;
 begin
  MH[MH_cnt]:=CM; 
  writeln(f);
  writeln(f,'First ',lmax,' macro steps:');
  writeln(f,' ind rule         c             LsdR');
  lim:=lmax;
  if lim>MH_cnt then lim:=MH_cnt;
  for i:=0 to lim do with MH[i] do begin
   write(f,i:4,rn:5,c:10,':  ');
   writeln(f,RevStr(l),SD_str(s,md),r);
  end; 
  writeln(f);
 end;
 
procedure wr_mhistory(var f:text; lmax:longint);
 begin wr_macro_history(f,CM,MH,MH_cnt,lmax) end;

procedure wr_brule(var f:text; var Rule:TBRule);
 var sd:string; k:word;
 begin with Rule do begin
   write(f,'ucnt   c  Rule[',id:2,']: ');
   sd:=SD_str(s,md);
   if md=0 
    then write(f,        '*(c0)'+sd+a+'*':12,'  -->  *'+sd+a+'(c1)*')
    else write(f,'*'+RevStr(a)+sd+'(c0)*':12,'  -->  *(c1)'+RevStr(a)+sd+'*');
   writeln(f); 
   if Patt_cnt>0 then for k:=0 to Patt_cnt-1 do with Patts[k] do begin
    write(f,ucnt:4,c:4,' ');
    if md=0 
     then writeln(f,RevStr(c0):23,'  -->  ',c1)
     else writeln(f,        c0:23,'  -->  ',RevStr(c1));
   end;
   writeln(f); 
 end end;

procedure wr_rule(
 var f:text; var Rule:TRule; all,full:boolean);
 var ws,l1,r1:string; k:word;
 begin 
  with Rule do if
   used or (all and (length(c0)+length(a)<26)) 
  then begin
   if full then write(f,id:4,p:4,c:4,':  ');
   l1:=SD_str(s,md); ws:=l1;
   if p<0 then begin ws[1]:=l1[2]; ws[2]:=l1[1] end;
   l1:='*'+RevStr(a)+ws+'('+c0+')*'; 
   r1:='*('+RevStr(c1)+')'+RevStr(a)+ws+'*';
   if p<0 then begin l1:=RevStr(l1); r1:=RevStr(r1) end;
   ws:=l1; 
   if full then while length(ws)<20 do ws:=' '+ws;
   ws:=ws+' -> '+r1;
   if full then while length(ws)<44 do ws:=ws+' ';
   write(f,ws);
   if full then begin
    write(f,' sp> ');
    if (not all) and used then 
     for k:=1 to spec_max do write(f,spectrum[k]:4);
   end;  
   writeln(f);
  end; 
 end;
 
procedure wr_rules(
 var f:text; name:string; var Rules:TRuleArr; R_cnt:longint; all:boolean);
 var i:word;
 begin 
  writeln(f);
  if not all then name:='used '+name;
  writeln(f,'List of the '+name+' rules:');
  writeln(f,' ind   p   c               pattern1       pattern2');
  if R_cnt>0 then for i:=0 to R_cnt-1 do wr_rule(f,Rules[i],all,true);
 end;
 
procedure SortRules;
 var i,j:longint; WR:TRule;
 function LessR(var R1,R2:TRule):boolean;
  begin
   if length(R1.c0)<length(R2.c0)
    then LessR:=true
    else if length(R1.c0)>length(R2.c0)
     then LessR:=false
     else LessR:=length(R1.a)>length(R2.a)
  end;
 begin 
  if SR_cnt>1 then for i:=0 to SR_cnt-2 do
  for j:=i+1 to SR_cnt-1 do 
  if LessR(SRules[i],SRules[j]) then begin
   WR:=SRules[i]; SRules[i]:=SRules[j]; SRules[j]:=WR
  end;
 end;

procedure SortBRules(id:longint);
 var i,j:longint; WR:TBRuleEl;
 begin with BSRules[id] do 
  for i:=0 to Patt_cnt-2 do
  for j:=i+1 to Patt_cnt-1 do 
  if length(Patts[i].c0)<length(Patts[j].c0) then begin
   WR:=Patts[i]; Patts[i]:=Patts[j]; Patts[j]:=WR
  end;
 end;

procedure ShiftTest;
 var 
  i,p_min,p_max:longint; 
  OK,BRuleFound,BStatRep:boolean;
  sst:array[1..dm] of longint;
  R0:TRule; { new simple rule }
  a0,a1,c0,c1:string;
 procedure SetRule(a0,c0,c1:string; f_use:boolean);
  var i:word; 
  function Repeated(s1,s2:string):boolean;
   var succ:boolean;
   begin
    succ:=true;
    while succ and (length(s1)<=length(s2)) do begin
     succ:=Pos(s1,s2)=1;
     delete(s2,1,length(s1));
    end;
    Repeated:=succ and (s2='');
   end;
  function Sim(s1,s2:string; appr:boolean):boolean;
   begin
    if appr
     then Sim:=(s1=s2) 
     else Sim:=Repeated(s1,s2); 
   end;
  function MemberR(var R:TRule; var RA:TRuleArr; rc:longint; appr:boolean):boolean;
   var i:longint;
   begin
    MemberR:=false;
    if rc>0 then for i:=0 to rc-1 do with RA[i] do
     if (s=R.s) and (md=R.md) and
        (a=R.a) and 
        Sim(c0,R.c0,appr) and Sim(c1,R.c1,appr)
      then MemberR:=true;
   end;
  procedure AddRule(var R0:TRule; rep:byte);
   var i:byte; ws:string; R1:TRule; 
   begin 
    R1:=R0;
    with R1 do begin
     c:=c*rep; p:=p*rep;
     ws:=''; for i:=1 to rep do ws:=ws+c0; c0:=ws;
     ws:=''; for i:=1 to rep do ws:=ws+c1; c1:=ws;
    end;
    if not MemberR(R1,SRules,SR_cnt,true) and (SR_cnt<rmax) then begin
     R1.id:=SR_cnt;
     SRules[SR_cnt]:=R1;
     inc(SR_cnt);
    end;
   end;

  function eqROL(s0,s1:string):boolean;
   var OK:boolean; 
   begin
    OK:=s0=s1; 
    eqROL:=OK; 
   end; 

  procedure Follow(var R0,R1:TRule);
   var nok0,f0,f1:longint; s0,s1:string; 
   procedure SetS(Var c,s:string; var rep:longint);
    var k:byte;
    begin
     rep:=nok0 div length(c); s:='';
     for k:=1 to rep do s:=s+c; 
    end;
   begin if R0.p*R1.p<0 then begin
    nok0:=nok(length(R0.c0),length(R1.c1));
    if nok0<sr_lmax then begin
     SetS(R0.c0,s0,f0);
     SetS(R1.c1,s1,f1);
     if eqROL(s0,s1) then begin
      AddRule(R0,f0);
      AddRule(R1,f1);
     end; 
    end; 
   end end;
   
  procedure ApproveRule;
   var i:longint;
   begin
    if ASR_cnt>0 then for i:=0 to ASR_cnt-1 do begin
     Follow(R0,ASRules[i]);
     Follow(ASRules[i],R0);
    end; 
   end;
  procedure AddRule0;
   begin 
    if not MemberR(R0,ASRules,ASR_cnt,false) and (ASR_cnt<rmax) then begin
     ApproveRule;
     R0.id:=ASR_cnt;
     ASRules[ASR_cnt]:=R0;
     inc(ASR_cnt);
    end;
   end;

  function GetBaseRule(s,d:byte; a:string):longint;
   var i,j:longint;
   begin
    j:=-1;
    if BSR_cnt>0 then for i:=0 to BSR_cnt-1 do
     if (BSRules[i].s=s) and
        (BSRules[i].md=d) and
        (BSRules[i].a=a) then j:=i;
    if j>=0 
     then GetBaseRule:=j 
     else if BSR_cnt<=bmax then begin
      j:=BSR_cnt; inc(BSR_cnt);
      GetBaseRule:=j;
      BSRules[j].s:=s;
      BSRules[j].md:=d;
      BSRules[j].a:=a;
      BSRules[j].id:=j;
      BSRules[j].Patt_cnt:=0;
     end else GetBaseRule:=j;
   end;
  procedure AddBaseRule;
   var id,i:longint; newrule,noaditive:boolean;
   
   procedure AditiveTest;
    var i:longint; cp:string; R:TRule; succ:boolean;
    begin
     R:=R0;
     repeat
      cp:=R.c0;
      succ:=true;
      with BSRules[id] do if Patt_cnt>0 then
       for i:=0 to Patt_cnt-1 do if succ then 
        if (R.c0<>'') and (Pos(Patts[i].c0,R.c0)=1)
         then begin
          delete(R.c0,1,length(Patts[i].c0));
          succ:=false;
         end; 
     until cp=R.c0;
     noaditive:=cp<>'';                                                                      
    end;

   const bmaxlen=dm+2 { dm_2 };

   begin 
    id:=GetBaseRule(R0.s,R0.md,R0.a);
    if id>=0 then begin
     AditiveTest; 
     
     newrule:=true;
     with BSRules[id] do if Patt_cnt>0 then 
      for i:=0 to Patt_cnt-1 do if R0.c0=Patts[i].c0 then newrule:=false;
      
     i:=BSRules[id].Patt_cnt;
     if newrule and (i<=bmax) and (length(R0.c0)<=bmaxlen) and 
        (f_use or
         (
          (length(BSRules[id].a)=0) and (length(R0.c0)<=bmaxlen) and 
          (
           ((not BStatRep) and (length(R0.c0)=R0.c)) or 
           (noaditive and (length(R0.c0)<R0.c)) 
          ) 
         )
        ) 
     then begin
      BRuleFound:=true;
      with BSRules[id].Patts[i] do begin
       c0:=R0.c0;
       c1:=R0.c1;
       c :=R0.c;
      end;
      inc(BSRules[id].Patt_cnt);
      if BSRules[id].Patt_cnt>1 then SortBRules(id);
     end;
     if BSRules[id].Patt_cnt=0 then dec(BSR_cnt);
    end;
   end;
   
  var j,k:word;
  begin
   R0.a :=a0; 
   R0.c0:=c0; R0.c1:=c1;
   i:=SR_cnt;
   AddRule0;
   if not BRuleFound then begin
    AddBaseRule;
    { BRuleFound:=true; }
   end; 
   if i<SR_cnt then begin
    if i>0 then for j:=0 to i-1 do for k:=i to SR_cnt-1 do begin
     Follow(SRules[k],SRules[j]);
     Follow(SRules[j],SRules[k]);
    end; 
    { SortRules; }
   end; 
  end;
 procedure TryRule(la,lc:longint; l,r,l1:string; f_use:boolean);
  begin 
   a0:=GetF(l,1,la); a1:=GetF(l1,1,la);
   if a0=a1 then begin
    c0:=GetF(r ,1,lc);
    c1:=GetF(l1,la+1,lc);
    if length(r)<=1 
     then begin e_state:=m_loop; OK:=true end;
    if e_state=0 then SetRule(a0,c0,c1,f_use)
   end;
  end;
 procedure TryCenter(la,lb:longint; l,r,l1,r1:string);
  begin 
   if (GetF(r,1,lb)=GetF(r1,1,lb)) and
      (GetF(l,1,la)=GetF(l1,1,la))
    then begin e_state:=c_loop; OK:=true end;
  end;
 var clmin,clmax,crmin,crmax:longint; 
 begin 
  if (CD.smax<250) and (SH_cnt<dm2qub) then begin
   for i:=1 to dm do sst[i]:=0;
   i:=SH_cnt; OK:=false; BRuleFound:=false; 
   p_min:=mmax+1; p_max:=-p_min;
   clmin:=i; clmax:=i; crmin:=i; crmax:=i; 
   BStatRep:=false;
   while (not OK) and (i>0) do begin
    dec(i);
    with SH[i] do begin

     inc(sst[s]);
     if sst[s]>1 then BStatRep:=true; 
      
     if p<=p_min then begin
      if p<p_min then clmax:=i;
      p_min:=p;
      clmin:=i;
     end; 
     if p>=p_max then begin
      if p>p_max then crmax:=i;
      p_max:=p;
      crmin:=i;
     end; 
     if (s=CD.s) and (md=CD.md) then begin { new rule ? }
      R0.p:=CD.p-p; R0.c:=CD.c-c; 
      R0.s:=s; R0.md:=md;
      
      if (R0.p>0) and (md=1) and (CD.p=p_max+1) { r_rule }
        then TryRule(p-p_min,CD.p-p,l,r,CD.l,crmin<=clmax);
      if (R0.p<0) and (md=0) and (CD.p=p_min-1) { l_rule }
        then TryRule(p_max-p,p-CD.p,r,l,CD.r,clmin<=crmax);
      if R0.p=0 then if md=1 { c_loop }
        then TryCenter(p-p_min,p_max+1-CD.p,l,r,CD.l,CD.r)
        else TryCenter(p-p_min+1,p_max-CD.p,l,r,CD.l,CD.r);
     end;
    end; 
   end;
  end; 
 end;

{ -------------------------------------------------------------}

procedure info0;
 var i:byte;
 begin
  gotoxy(3,1); write(m:10);
  gotoxy(55,1); 
  write('V = ',m div (get_sec - old_sec + 1):4,' machines/sec ');
  for i:=1 to e_max do 
    begin gotoxy(5,i+1); write(e_cnt[i]:8) end;
 end;

{ -------------------------------------------------------------}

procedure InvSTest;
 var i,j:byte;
 function S(k:byte):byte;
  begin if k=j then S:=i else S:=k end;
 begin
  for i:=1 to dm-1 do for j:=i+1 to dm do 
   if ((C[i]=C[j]) and (C[i]<>dum)) and
      ((C[i+dm]=C[j+dm]) and (C[i+dm]<>dum)) and
      ((B[i]=B[j]) and (B[i]<>dum)) and
      ((B[i+dm]=B[j+dm]) and (B[i+dm]<>dum)) and
      ((S(A[i])=S(A[j])) and (A[i]<>dum)) and
      ((S(A[i+dm])=S(A[j+dm])) and (A[i+dm]<>dum)) 
    then e_state:=i_loop;  
 end;
 
procedure back_track;
  const bt_sz=4; bt_sz2=bt_sz+bt_sz; bt_sz2s=bt_sz2+1;
        bt_max=16; sp_max=08;
  {
  const bt_sz=8; bt_sz2=bt_sz+bt_sz; bt_sz2s=bt_sz2+1;
        bt_max=32; sp_max=16;
  }      
  type st=array[0..bt_sz2] of byte;
       s_rec=record t:st; ct,j,p:byte end;
  var v,w:s_rec;
      Stack:array[0..sp_max] of s_rec;
      sp:byte; end_bt:boolean;
  procedure bt_push;
   begin
    if sp<=sp_max
     then begin Stack[sp]:=w; inc(sp) end
     else end_bt:=true
   end;
  procedure bt_pull;
   begin dec(sp); v:=Stack[sp] end;
  procedure bt_0;
   var i,j,bb:byte;
   procedure bt1;
    var x:byte;
    begin
     w.j:=j; inc(w.ct);
     if w.ct>=bt_max then end_bt:=true;
     x:=w.t[w.p];
     if (x=dum) or (x=C[i]) or (C[i]=dum)
      then begin w.t[w.p]:=bb; bt_push end;
    end; { bt1 }
   procedure bt_l;
    begin if w.p<bt_sz2 then begin inc(w.p); bt1 end else end_bt:=true end;
   procedure bt_r;
    begin if w.p>0 then begin dec(w.p); bt1 end else end_bt:=true end;
   begin { bt_0 }
    i:=0;
    repeat
     inc(i);
     if v.j=A[i] then begin
      w:=v; j:=i;
      if i>dm then begin j:=j-dm; bb:=1 end else bb:=0;
      if B[i]<>dum
       then if B[i]=0 then bt_l else bt_r
       else begin bt_l; w:=v; bt_r end;
     end;
    until (i=dm_2) or end_bt;
   end; { bt_0 }
  begin { back_track }
   fillchar(w.t,bt_sz2s,chr(dum));
    { for i:=0 to bt_sz2 do w.t[i]:=dum; }
   sp:=0; w.p:=bt_sz; w.ct:=0;
   w.j:=0;   bt_push; 
   w.j:=dum; bt_push; { Have i need this ??? }
   end_bt:=false;
   repeat bt_pull; bt_0 until end_bt or (sp=0);
   if not end_bt then e_state:=b_loop;
  end; { back_track }

function lDum:boolean;
 var i,k:byte;
 begin
  k:=0;
  for i:=1 to dm_2 do if A[i]=dum then inc(k);
  lDum:=k<2;
 end;

{ -------------------------------------------------------------}

var new_def:boolean;

procedure MakeMStep0(var D:TDescr; macro:byte); 
 var k,ko,s1,v1,d1,v0:byte; sstep:boolean;

 procedure ch_state;
  var l,n,o:byte; b:boolean;
  function lnk(n:byte):boolean;
   var x:array[1..dm] of boolean; l:byte; b,b1:boolean;
   procedure d(n:byte);
    begin
     if n=dum then b:=true
      else if n>0 then if not x[n] then begin
       x[n]:=true; d(A[n]); d(A[n+dm]) end
    end;
   begin
    for l:=1 to dm do x[l]:=false;
    b:=false; d(n); b1:=true;
    for l:=1 to dm do if not x[l] then b1:=false;
    lnk:=b or b1;
   end; { lnk }
  begin  { ch_state }
   l:=dm+1; if k>dm then n:=k-dm else n:=k;
   repeat dec(l); b:=(A[l]=dum) and (A[l+dm]=dum) and (l>n) until not b;
   if l<dm then inc(l);
   for o:=1 to l-1 do begin
    A[k]:=o; if lnk(n) then push(chr(ord('0')+o)) end;
   A[k]:=l; s1:=l; if not lnk(n) then e_state:=s_loop;
  end; { ch_state }

 begin
  pr_fail:=false;
  case macro of
   0:sstep:=true;
   1:sstep:=not SuccMStep(D,SRules,SR_cnt);
   2:sstep:=not SuccBStep(D);
   3:sstep:=not SuccMStep(D,SSRules,SSR_cnt);
  end; 
  
  if sstep then begin
  
   with D do if md=0 then UnpackFirst(l) else UnpackFirst(r);
   v0:=GetDV(D);
   D.rname:=chr(ord('@')+D.s)+V_str[v0];
   if v0=0 then k :=D.s else k :=D.s+dm;
   if v0=1 then ko:=D.s else ko:=D.s+dm;
   v1:=C[k]; 
   if v1=dum then if D.af 
    then pr_fail:=true
    else if A[k]=0 
     then v1:=0
     else begin C[k]:=0; push('_'); C[k]:=1; v1:=1; new_def:=true end;
   s1:=A[k]; 
   if s1=dum then if D.af 
    then pr_fail:=true
    else begin ch_state; new_def:=true end;
   d1:=B[k]; 
   if d1=dum then if D.af 
    then pr_fail:=true
    else if (A[k]=0) or (e_state>0) 
     then d1:=0
     else begin 
      B[k]:=0; 
      if SameDir then B[ko]:=0;
      push('<'); 
      B[k]:=1; 
      if SameDir then B[ko]:=1;
      d1:=1; new_def:=true 
     end;
     
   if (not pr_fail) then MakeDStep(D,s1,v1,d1,macro);

   with D do if (not af) then 
    if p<p_left then p_left:=p
    else if p>p_right then p_right:=p;
   
   if s1=0 then if D.af then pr_fail:=true else e_state:=nm_end;
  end;
 end;

procedure MakeMStep(var D:TDescr); 
 begin
  {
  if rule_min>dm_2 
   then repeat  MakeMStep0(D,1) until D.rn>=0
   else
  } 
  MakeMStep0(D,1);
  if (not D.af) then TryInfinity(D);
 end;

procedure ClearDescr(var D:TDescr);
 begin with D do begin
  md:=0; s:=1;
  l:='.'; r:='.';
  c:=0; p:=0;
  af:=false;
  rn:=-1; 
  rname:='--';
  smax:=0;
  {
  r_mark:='.<A.';
  l_mark:=r_mark;
  }
 end end;
 
{ -------------------------------------------------------------}

const
 ptran_max=400;

function eqDes(var D1,D2:TDescr):boolean;
 begin
  eqDes:=
   (D1.s=D2.s) and
   (D1.md=D2.md) and
   (D1.l=D2.l) and
   (D1.r=D2.r) and
   (D1.p=D2.p)
 end;

{ ---------- New Pos test: ------------- } 
 
type
 TPosString = record
  mode:byte;  { 0 - left 1 - center 2 - right }
  md:byte;    { 0/1 - rigth/left accessibility }
  s:string;
 end;
 TPosDescr = record
  mode:byte;
  a,b,n:longint; { left/right end, length }
 end;
 TPosTran_3 = record
  D,DNext:TDescr;
  str_l,str_r: longint; { pointers to PStrArr }
  mod_l,mod_c,mod_r: TPosDescr;
  a,b:longint; { left/right end }
 end;
 TPosTuple = record
  i,j:longint; { pointers to PStrArr }
 end; 

var
 PStrArr: array[0..ptran_max] of TPosString;
 PStr_cnt: longint;
 PTupleArr: array[0..gfin_max] of TPosTuple;
 PTuple_cnt: longint;
 PTArr_3: array[0..gfin_max] of TPosTran_3;
 PTA_cnt3:longint;

procedure wr_postran_3(var f:text; i:longint; var PT:TPosTran_3);
 begin with PT do begin
   write(f,
    i:3,' ',
    mod_l.mode,'-',mod_c.mode,'-',mod_r.mode,' ',
    str_l:3,' ',str_r:3,' ',
    a+1:4,b:4,D.p:6,DNext.p:6,DNext.c:6,':  ');
   with D     do   write(f,RevStr(l)+SD_str(s,md)+r:15,'   -->   ');
   with DNext do writeln(f,RevStr(l)+SD_str(s,md)+r);
 end end;
 
procedure wr_pproof_3(var f:text);
 var i:longint;
 begin
  writeln(f);
  writeln(f,'Position words:');
  writeln(f,' id mode  md       string');
  for i:=0 to PStr_cnt-1 do with PStrArr[i] do
   writeln(f,i:3,'   ',mode,'    ',md,'    ',s);
  writeln(f); 
  writeln(f,'Tuples:');
  writeln(f,' id  i0  j0');
  for i:=0 to PTuple_cnt-1 do 
   writeln(f,i:3,' ',PTupleArr[i].i:3,' ',PTupleArr[i].j:3);
  writeln(f); 
  writeln(f,'Position_3 proof:');
  writeln(f,'  i  mode  s_l s_r   a   b p_old p_new     c');
  if PTA_cnt3>0 then for i:=0 to PTA_cnt3-1 
   do wr_postran_3(f,i,PTArr_3[i]);
 end;
 
function EqPStr(var p1,p2:TPosString):boolean;
 begin
  EqPStr:=
   (p1.mode=p2.mode) and (p1.md=p2.md) and (p1.s=p2.s)
 end;
function EqPDescr(var p1,p2:TPosDescr):boolean;
 begin
  EqPDescr:=
   (p1.mode=p2.mode) and (p1.a=p2.a) and (p1.b=p2.b)
 end;
 
function PStrId(var PS:TPosString):longint;
 var i,n:longint; found:boolean; 
 begin
  found:=false; n:=-1;
  if PStr_cnt>0 then for i:=0 to PStr_cnt-1 do
   if EqPStr(PStrArr[i],PS) 
    then begin found:=true; n:=i end;
  if not found then if PStr_cnt>ptran_max
   then pr_fail:=true
   else begin
    PStrArr[PStr_cnt]:=PS;
    {
    writeln(ttm,'Str[',PStr_cnt,'] ==> mode=',PS.mode,' md=',PS.md,' s=',PS.s);
    }
    n:=PStr_cnt; inc(PStr_cnt); 
   end; 
  PStrId:=n; 
 end;

procedure AddPTuple(i0,j0:longint);
 var k:longint; found:boolean; 
 begin
  found:=false;
  for k:=0 to PTuple_cnt-1 do with PTupleArr[k] do
   if (i=i0) and (j=j0) then found:=true;
  if not found then if PTuple_cnt>gfin_max
   then pr_fail:=true
   else begin
    with PTupleArr[PTuple_cnt] do 
     begin i:=i0; j:=j0 end;
    inc(PTuple_cnt); 
   end;
 end;
 
function eqTPT_3(var D1,D2:TPosTran_3):boolean;
 begin
  eqTPT_3:=eqDes(D1.D,D2.D) and
   (D1.a=D2.a) and
   (D1.b=D2.b) and
   (D1.str_l=D2.str_l) and
   (D1.str_r=D2.str_r) and
   EqPDescr(D1.mod_l,D2.mod_l) and
   EqPDescr(D1.mod_c,D2.mod_c) and
   EqPDescr(D1.mod_r,D2.mod_r)
 end;

procedure TryP_3(PosAl,PosBl,PosAr,PosBr:longint);
 var
  PT:TPosTran_3;
  old_PTA_cnt,old_scnt,old_tcnt,i:longint; closed:boolean;
  modes:array[0..2] of TPosDescr;  

 procedure Loop0;
  const rmax1=rmax;
  var 
   DArr:array[0..rmax1] of TDescr;
   D_cnt:longint;
  procedure SearchD(var D:TDescr);
   var i:longint; found:boolean;
   begin
    found:=false;
    if D_cnt>0 then for i:=0 to D_cnt-1 do
     if eqDes(DArr[i],D) then found:=true;
    if not found then if D_cnt>rmax1
     then pr_fail:=true
     else begin
      DArr[D_cnt]:=D;
      inc(D_cnt)
     end; 
    if found then pr_fail:=true; 
   end;
  begin with PT do begin
   D_cnt:=0; D.c:=0;
   repeat
    MakeMStep0(D,0);
    SearchD(D); 
   until pr_fail or
         ((D.p<=a)   and (D.md=0)) or
         ((D.p>=b+1) and (D.md=1));
  end end;

 function CutStr(s:string; b,l:longint):string;
  var w:string;
  begin
   w:=s;
   delete(w,1,b);
   w:=copy(w,1,l);
   {
   if w[length(w)]<>'.' then w:=w+'.';
   }
   if w[length(w)]='.' then delete(w,length(w),1);
   while length(w)<l do w:=w+'-';
   w:=w+'.';
   CutStr:=w;
  end;
  
 procedure AddTran1(var PT:TPosTran_3);
  var i:longint; found:boolean; PT1:TPosTran_3;
  begin
   PT1:=PT;
   with PT1 do begin b:=b-a; D.p:=D.p-a; a:=0 end; 
   found:=false;
   if PTA_cnt3>0 then for i:=0 to PTA_cnt3-1 do
    if eqTPT_3(PTArr_3[i],PT1) then found:=true;
   if not found then if PTA_cnt3>gfin_max
    then pr_fail:=true
    else begin
     PTArr_3[PTA_cnt3]:=PT1;
     inc(PTA_cnt3)
    end; 
  end;
  
 procedure Shift0;
  var 
   a0,b0,c0:TPosString;
   ci,bi,k,str_old,a_old:longint;
   m_old:TPosDescr;
  begin with PT do begin
   with c0 do begin
    s:=CutStr(D.r,mod_l.n+mod_c.n,mod_r.n);
    mode:=mod_r.mode; md:=0;
   end;
   with b0 do begin
    s:='S'+CutStr(D.r,mod_l.n,mod_c.n);
    mode:=mod_c.mode; md:=0;
   end;
   ci:=PStrId(c0); bi:=PStrId(b0); 

   for k:=0 to PTuple_cnt-1 do with PTupleArr[k] do
    if str_r=i then AddPTuple(ci,j);
    
   AddPTuple(bi,ci); 
   str_r:=bi;
   D.r:=CutStr(D.r,0,mod_l.n+mod_c.n);
   m_old:=mod_r; mod_r:=mod_c; mod_c:=mod_l;
   inc(D.p,m_old.n); D.c:=0;
   str_old:=str_l; a_old:=a;
   for k:=0 to PTuple_cnt-1 do with PTupleArr[k] do
    if str_old=i then begin
     a0:=PStrArr[j]; str_l:=j;
     mod_l:=modes[a0.mode];
     D.l:=a0.s;
     a:=a_old+m_old.n-mod_l.n;
     if a0.s[1]<>'S' then AddTran1(PT);     
    end;
  end end;

 procedure Shift1;
  var 
   a0,b0,c0:TPosString;
   ai,bi,k,str_old,b_old:longint;
   m_old:TPosDescr;
  begin with PT do begin
   with a0 do begin
    s:=CutStr(D.l,mod_r.n+mod_c.n,mod_l.n);
    mode:=mod_l.mode; md:=1;
   end;
   with b0 do begin
    s:='S'+CutStr(D.l,mod_r.n,mod_c.n);
    mode:=mod_c.mode; md:=1;
   end;
   ai:=PStrId(a0); bi:=PStrId(b0); 
   
   for k:=0 to PTuple_cnt-1 do with PTupleArr[k] do
    if str_l=i then AddPTuple(ai,j);
    
   AddPTuple(bi,ai); 
   str_l:=bi;
   D.l:=CutStr(D.l,0,mod_r.n+mod_c.n);
   m_old:=mod_l; mod_l:=mod_c; mod_c:=mod_r;
   dec(D.p,m_old.n); D.c:=0;
   str_old:=str_r; b_old:=b;
   for k:=0 to PTuple_cnt-1 do with PTupleArr[k] do
    if str_old=i then begin
     c0:=PStrArr[j]; str_r:=j;
     mod_r:=modes[c0.mode];
     D.r:=c0.s;
     b:=b_old-m_old.n+mod_r.n;
     if c0.s[1]<>'S' then AddTran1(PT);     
    end;
  end end;

 procedure Loop;
  begin with PT do begin
   Loop0;
   PTArr_3[i].DNext:=D;
   {
   wr_postran_3(ttm,i,PTArr_3[i]);
   } 
   if not pr_fail then if ((D.p<=a) and (D.md=0))
    then Shift0 else Shift1;
  end end;

 begin
  with modes[0] do begin mode:=0; a:=-PosBl; b:=-PosAl end;
  with modes[1] do begin mode:=1; a:=-PosAl; b:= PosAr end;
  with modes[2] do begin mode:=2; a:= PosAr; b:= PosBr end;
  for i:=0 to 2 do with modes[i] do n:=b-a;
  with PStrArr[0] do begin s:='.'; mode:=0; md:=1 end;
  with PStrArr[1] do begin s:='.'; mode:=2; md:=0 end;
  PStr_cnt:=2;
  with PTupleArr[0] do begin i:=0; j:=0 end;
  with PTupleArr[1] do begin i:=1; j:=1 end;
  PTuple_cnt:=2;
  
  { 
  writeln(ttm,'ABlr= ',-PosBL,' ',-PosAl,' ',PosAr,' ',PosBr);
  writeln(ttm,'ExLens= ',modes[0].n,' ',modes[1].n,' ',modes[2].n);
  } 
   
  old_PTA_cnt:=0;
  old_scnt:=0;
  old_tcnt:=0;
  repeat
   PTA_cnt3:=1; i:=0;
   pr_fail:=false;
   with PTArr_3[0] do begin
    ClearDescr(D); 
    D.af:=true;
    str_l:=0; str_r:=1;
    mod_l:=modes[0];
    mod_c:=modes[1];
    mod_r:=modes[2];
    a:=-PosBl; 
    b:=PosBr;
   end;
   while (not pr_fail) and (i<PTA_cnt3) do begin
    PT:=PTArr_3[i]; 
    Loop;
    inc(i);
   end;
   closed:=
    (PTA_cnt3=old_PTA_cnt) and
    (PStr_cnt=old_scnt) and
    (PTuple_cnt=old_tcnt);
   if not closed then begin
    old_PTA_cnt:=PTA_cnt3;
    old_scnt:=PStr_cnt;
    old_tcnt:=PTuple_cnt;
   end; 
  until pr_fail or closed;

  if not pr_fail then begin
   writeln(ttm,'M=',m,' gfin_3 PosLR= ',
           PosAl,'-',PosBl,'  ',PosAr,'-',PosBr);
   flush(ttm);        
   e_state:=pfin_l;
  end; 

  { wr_pproof_3(ttm); }
 end;

{ ---------- Old Pos parts: ------------- } 
 
{
function eq(var R1,R2;SZ:word):boolean;
 var
  i:longint;
  A:array[word] of char absolute R1;
  B:array[word] of char absolute R2;
 begin
  eq:=true;
  for i:=0 to SZ-1 do if A[i]<>B[i] then eq:=false;
 end;
}

procedure TryPFin_2;
 var dL,dR,d_l,d_r:longint; 

 procedure TryNext;
  begin
   if (e_state<>pfin_l) then begin
    e_state:=0;
    { TryP(PosAl+d_l,PosBl+d_l,PosAr+d_r,PosBr+d_r); }
    TryP_3(PosAl+d_l,PosBl+d_l,PosAr+d_r,PosBr+d_r); 
   end;
  end;
 begin
  EvalPSCnt;

  {
  WrPosStat(ttm);
  }
  
  if ((PosAl>=0) or (pst_min>-16)) and
     ((PosAr>=0) or (pst_max<16))  then begin

   if PosAl<0 then begin PosAl:=PosAr; PosBl:=PosBr end;
   if PosAr<0 then begin PosAr:=PosAl; PosBr:=PosBl end;
     
   if PosAl<0 then begin PosAl:=2; PosBl:=PosAl+2 end; 
   if PosAr<0 then begin PosAr:=2; PosBr:=PosAr+2 end;

   while PosBl-PosAl in [1{,2}] do inc(PosBl,PosBl-PosAl); 
   while PosBr-PosAr in [1{,2}] do inc(PosBr,PosBr-PosAr); 
   
   dL:=PosBl-PosAl; if dL>0 then dec(dL);
   dR:=PosBr-PosAr; if dR>0 then dec(dR);

   {
   writeln(ttm,'Bl Al = ',PosBl,' ',PosAl);
   writeln(ttm,'Br Ar = ',PosBr,' ',PosAr);
   }

   { dL:=dL+dL; dR:=dR+dR; }

   {
   for d_l:=1-PosAl to dL do for d_r:=1-PosAr to dL do TryNext;
   }

   while PosAl>1 do begin dec(PosAl); dec(PosBl) end;
   while PosAr>1 do begin dec(PosAr); dec(PosBr) end;
   
   for d_l:=0 to dL do for d_r:=0 to dL do TryNext;
   
  end;
 end;

procedure TryPFin_2_all(dim:word);
 var dL,dR,d_l,d_r,PBl,PBr,dim_1,i0,i1:longint; 
 procedure TryNext;
  begin
   if (e_state<>pfin_l) then begin
    e_state:=0;
    TryP_3(PosAl+d_l,PosBl+d_l,PosAr+d_r,PosBr+d_r); 
   end;
  end;
 begin
  PosAl:=1; PosAr:=1;

  if dim>dm then dim_1:=dim+dm else dim_1:=dim;

  {
  for PBl:=PosAl+2 to PosAl+dim_1+2 do
  for PBr:=PosAr+2 to PosAr+dim_1+2 do 
  }

  for i0:=0 to dim_1 do for i1:=0 to dim_1 do
  if (e_state<>pfin_l) and
     ((i0<dim) or (i1<dim))
  then begin
   PBl:=PosAl+2+i0;
   PBr:=PosAr+2+i1;
   PosBl:=PBl; PosBr:=PBr;
   gotoxy(55,5); write('PosLR=',PosBl,'|',PosBr,'  ');
   
   dL:=PosBl-PosAl; 
   if dL>dm then dL:=dm; if dL>0 then dec(dL); 
   dR:=PosBr-PosAr; 
   if dR>dm then dR:=dm; if dR>0 then dec(dR); 

   for d_l:=0 to dL do for d_r:=0 to dL do TryNext;
   
  end;
 end;

{ -------------------------------------------------------------}

const
 ESet_max = 1000 {3000} {5000} {10000};
 TIntroneStrLen=60;
 
type
  TIntronArr = array[0..bmax] of string[TIntroneStrLen];
  { TIntroneStrLen must be enough for TryBL_Proof intrones !!! }

  TExoneSet = record
   EA:TIntronArr;
   cnt:longint
  end; 
  
var
  MainRule:TBRule;
  MSRule,OSRule:TRule;

  BBR_id:longint;
  BBG,BBGs:TGraph;
  BBG_cnt,BBGs_cnt:longint;

  IntronI, IntronO: TIntronArr;
  InI_cnt, InO_cnt: longint;
  Lexones, Rexones: TIntronArr;
  Lex_cnt, Rex_cnt: longint;
  Lex_id, Rex_id, LR_mod:word;

procedure AddIntron(var IntrIO:TIntronArr; var In_cnt:longint; newIntr:string);
 var i:longint; found:boolean;
 begin
  found:=false;
  if In_cnt>0 then for i:=0 to In_cnt-1 do
   if IntrIO[i]=newIntr then found:=true;
  if not found then 
  if (In_cnt<bmax) and (length(newIntr)<=TIntroneStrLen) then begin
   IntrIO[In_cnt]:=newIntr;
   inc(In_cnt);
  end else pr_fail:=true;
 end;


procedure wr_brules(
 var f:text; name:string; var Rules:TBRuleArr; R_cnt:longint; all:boolean);
 var i:longint;
 procedure wr_intr(var IntrIO:TIntronArr; In_cnt:longint; name:string);
  var i:longint;
  begin if In_cnt>0 then begin
   write(f,name);
   for i:=0 to In_cnt-1 do write(f,IntrIO[i],'  ');
   writeln(f);
  end end;
 begin 
  writeln(f);
  if not all then name:='used '+name;
  writeln(f,'List of the '+name+' rules:');
  if R_cnt>0 then for i:=0 to R_cnt-1 do wr_brule(f,Rules[i]); 
  if BBR_id>=0 then begin
   writeln(f,'Main rule:');
   wr_brule(f,MainRule);
   wr_intr(IntronI,InI_cnt,'I_intrones = ');
   wr_intr(IntronO,InO_cnt,'O_intrones = ');
   wr_rules(f,'opposite',OSRules,OSR_cnt,true);
   writeln(f);
   case MainRule.nice of
    1:writeln(f,'Unknown machine type !');
    2:writeln(f,'Vortex at corner machine type !');
   end;
  end; 
  flush(f);
 end;

procedure MakeBStep(var DF:TDescr);
 var simple:boolean; rnam0,rnam1:string;

 function OldVertex(var CTG:TGraph; CTG_cnt:longint):boolean;
  var j:longint; 
  begin
   OldVertex:=false;
   for j:=0 to CTG_cnt-1 do if SimMacro2(DF,CTG[j].D)
    then OldVertex:=true;
  end;
 procedure AddVertex(var CTG:TGraph; var CTG_cnt:longint);
  begin
   if not OldVertex(CTG,CTG_cnt) then if CTG_cnt<gfin_max then begin
    CTG[CTG_cnt].D:=DF;
    CTG[CTG_cnt].checked:=false;
    inc(CTG_cnt);
   end else e_state:=too_lng;
  end;

 procedure MakeBLoopStep;
  function PackR(var r:string; io:boolean):boolean;
   var j:longint; c0a,c0b:string; w:char;
   begin
    PackR:=false;
    with MainRule do for j:=0 to Patt_cnt-1 do begin
     if io then c0b:=Patts[j].c0 else c0b:=Patts[j].c1;
     c0a:=GetF(r,1,length(c0b));
     if c0a=c0b then begin
      delete(r,1,length(c0a));
      if r='' then r:='.';
      if Pos('[',r)=1 
       then delete(r,1,1) 
       else IncS(']',r,DF.af) { r:=']'+r };
      w:=chr(ord('0')+j); 
      r:='['+w+r;
      if io then rnam1:='i' else rnam1:='o';
      rnam1:=rnam1+'+'+w;
      PackR:=true;
     end;
    end; 
   end;
  procedure TestI(var l,r:string);
   var w:char;
   begin 
    with MainRule do if Pos('[',r)=1 then begin
     if not simple then begin
      w:=r[2]; delete(r,1,2);
      if w='*' then begin
       e_state:=mem_ov;
       {
       gotoxy(1,23);
       writeln('Unpacking of * is disabled !');
       Halt;
       }
       w:=chr(ord('0')+m_id);
      end; 
      if r[1]=']' then delete(r,1,1) else r:='['+r;
      IncS(Patts[ord(w)-ord('0')].c0,r,DF.af);
      rnam0:='i-'+w;
     end;
     simple:=not simple;
    end else simple:=true;
   end;
  procedure TestO(var l,r:string);
   var 
    w,wc:char; orule:boolean; n,n1,k:longint; a1:string;
    TR:TRule;
   begin 
    with MainRule do if Pos('[',l)=1 then begin
     orule:=false;
     if not simple then begin
      wc:=l[2]; delete(l,1,2); 
      if wc='*' then w:=chr(ord('0')+m_id) else w:=wc;
      n:=ord(w)-ord('0');
      n1:=Pos('[',r);
      if n1>0 then a1:=copy(r,1,n1-1) else a1:=copy(r,1,length(r)-1);
      if OSR_cnt>0 then for k:=0 to OSR_cnt-1 do
       with OSRules[k] do if (s=DF.s) and (a=a1) and (c0=Patts[n].c1) 
         then begin TR:=OSRules[k]; orule:=true end;
      if orule then begin
       k:=1; 
       while l[1]=w do begin inc(k); delete(l,1,1) end;
       if l[1]=']' then delete(l,1,1) else l:='['+l;
       delete(r,1,length(a1));
       if r='.' then r:=']'+r else delete(r,1,1);
       while k>0 do begin 
        IncS(wc,r,DF.af);
        dec(k); 
        DF.c:=DF.c+TR.c;
        DF.p:=DF.p+TR.p;
       end;
       r:=a1+'['+r;
       rnam0:='O-'+w; rnam1:='I+'+w;
      end else begin
       if wc='*' then begin
        e_state:=mem_ov;
        {
        gotoxy(1,23);
        writeln('Unpacking of * is disabled !');
        Halt;
        }
       end;
       if l[1]=']' then delete(l,1,1) else l:='['+l;
       IncS(Patts[n].c1,l,DF.af);
       rnam0:='o-'+w;
      end; 
     end;
     if not orule then simple:=not simple;
    end else simple:=true;
   end;
  procedure Test(var l,r:string);
   var wI:string; n:byte; pack:boolean; wc:char;
   begin with MainRule do begin
 
    if (DF.md=md) 
     then pack:=PackR(l,false)
     else pack:=PackR(r,true);
    if not pack then begin
     if (DF.s=s) and (DF.md=md) and (Pos('[',r)=1) 
     then begin
      if not simple then begin
       delete(r,1,1); n:=Pos(']',r);
       wI:=copy(r,1,n-1); delete(r,1,n); 
       if Pos('[',l)=1 then delete(l,1,1) else l:=']'+l;
       while wI<>'' do begin
        wc:=wI[1]; IncS(wc,l,DF.af);
        if wc='*' then wc:=chr(ord('0')+m_id);
        n:=ord(wc)-ord('0');
        delete(wI,1,1);
        DF.c:=DF.c+Patts[n].c;
        if md=1 
         then DF.p:=DF.p+length(Patts[n].c0)
         else DF.p:=DF.p-length(Patts[n].c0);
       end;
       l:='['+l;
       rnam1:='m+*';
       rnam0:='m-*';
      end;
      simple:=false;
     end else if DF.md=md 
      then TestI(l,r)
      else TestO(l,r);
    end else simple:=false;  
    if simple then MakeMStep0(DF,0);  
   end end;
  begin
   if MainRule.md=1 
    then Test(DF.l,DF.r)
    else Test(DF.r,DF.l);
  end;
  
 begin
  rnam0:='   '; rnam1:='   ';
  BBGs_cnt:=1; BBGs[0].D:=DF;   
  simple:=false; 
  repeat
   MakeBLoopStep;
   if simple then if OldVertex(BBGs,BBGs_cnt)
    then e_state:=b_loop
    else AddVertex(BBGs,BBGs_cnt);
  until (not simple) or (e_state>0);
  DF.rname0:=rnam0;
  DF.rname1:=rnam1;
 end;

procedure wrf_m(var f:text; hd,sc:boolean; tstr:string); forward;

procedure ClearBRCntrs;
 var i,j:longint;
 begin
  for i:=0 to BSR_cnt-1 do with BSRules[i] do begin
   ucnt:=0;
   for j:=0 to Patt_cnt-1 do Patts[j].ucnt:=0;
  end; 
 end;

procedure VortexLoop(
 var CD:TDescr; var MH:THistory; var MH_cnt:longint; 
 mmode:byte; lim:longint);
 function PackTest:boolean;
  procedure Pack(var l:string);
   var w:char;
   begin 
    w:=chr(ord('0')+MainRule.m_id); 
    if l[1]='[' then begin
     if l[2]=w then l[2]:='*';
     while l[3]=w do delete(l,3,1);
    end;
   end;
  begin with MainRule do begin
   if (s=CD.s) and (md=CD.md) then begin
    PackTest:=true;
    case md of
     0:if CD.l='.' then Pack(CD.r);
     1:if CD.r='.' then Pack(CD.l);
    end; 
   end else PackTest:=false;
  end end;
 begin
  ClearDescr(CD);
  MH_cnt:=0;
  new_def:=false;
  e_state:=0;
  repeat
   MH[MH_cnt]:=CD; inc(MH_cnt); 
   repeat
    MakeBStep(CD);
    if MH_cnt>=lim then e_state:=too_lng;
    if new_def and (e_state=0) then begin
     InvSTest;
     if (e_state=0) and lDum then back_track;
     new_def:=false;
    end;
   until (e_state>0) or PackTest; 
  until e_state>0;
 end;

{ --------------- Swiming position test ------------------ }

const 
 PSwim_max=30;
type
 TContext = record s:byte; w:string end;
 WordArr = array[0..PSwim_max] of string;
 ContArr = array[0..PSwim_max] of TContext;
 
var
 Iwords, Owords: WordArr;
 Iw_cnt, Ow_cnt: longint;

{ ---------------- Bin Vortex test ------------------- }

var 
  L1r1,L1r2,L1r3,L1r4:string;

procedure wr_bmhistory(var f:text; lmax:longint);
 var i,lim:longint; 
 begin
  write(f,'MainShift single rule: ');
  wr_rule(f,MSRule,true,false);
  write(f,'Opposite  single rule: ');
  wr_rule(f,OSRule,true,false);

  writeln(f,'Macro_words near the main sequence (noted with *):');
  for i:=0 to Iw_cnt-1 do write(f,chr(ord('0')+i),'=',Iwords[i],'  ');
  writeln(f);
  
  writeln(f,'Macro_words opposite to the main sequence:');
  for i:=0 to Ow_cnt-1 do write(f,chr(ord('0')+i),'=',Owords[i],'  ');
  writeln(f);

  writeln(f,'Lemma1 rules:');
  writeln(f,'   '+L1r1);
  writeln(f,'   '+L1r2);
  writeln(f,'   '+L1r3);
  writeln(f,'   '+L1r4);
 
  BMH[BMH_cnt]:=BMM; 
  lim:=lmax;
  if lim>BMH_cnt then lim:=BMH_cnt;
  writeln(f);
  writeln(f,'First ',lmax,' bin_main_macro steps:');
  writeln(f,' ind     p         c             LsdR');
  for i:=0 to lim do with BMH[i] do begin
   write(f,i:4,' ',p:6,c:10,':  ');
   writeln(f,TD_str(BMH[i]));
  end; 
  writeln(f);
 end;

procedure BVortexLoop(lim:longint);
 const st_max = 800;
 var 
   CD:TDescr; i:longint; fail:boolean;
   Lemma1, L1Proved:boolean; b_id:longint; 
   S_F,S_B:byte; L1wz,L1wv,L1w0,L1w1:char;
   
 procedure MakeStep;
  begin
   MakeMStep0(CD,0); inc(i);
   if i>=st_max then e_state:=too_lng;
   if new_def and (e_state=0) then begin
    InvSTest;
    if (e_state=0) and lDum then back_track;
    new_def:=false;
   end;
   if CD.s=0 then fail:=true;
   if e_state>0 then fail:=true;
  end;
 function AddWord(s:string; var WArr:WordArr; var cnt:longint):char;
  var j:longint; found:boolean; 
  begin
   found:=false;
   if cnt>0 then for j:=0 to cnt-1 do if s=WArr[j] 
    then begin found:=true; AddWord:=chr(ord('0')+j) end;
   if not found then if cnt<PSwim_max then begin
    WArr[cnt]:=s;
    AddWord:=chr(ord('0')+cnt);
    inc(cnt);
   end else fail:=true;
  end;
 procedure PLoop(var l,r:string); 
  var 
   l1,ocont,oc0:string; n,k:byte;
   j1:longint;
  function TestI:boolean;
   begin
    TestI:=(CD.s=MSRule.s) and (CD.md=MSRule.md)
           and (r='.') and (GetF(l,1,n)=oc0) 
   end;
  function TestO:boolean;
   begin TestO:=(CD.md=1-MSRule.md) and (l='*.') end;
  procedure Unpck0(var s:string; var WArr:WordArr);
   var w:char;
   begin
    w:=s[1]; delete(s,1,1);
    if w in digits 
     then s:=WArr[ord(w)-ord('0')]+s 
     else fail:=true;
   end;
  procedure SingleLoop;
   var fin:boolean; packs:string; j:longint;
   function TestU:boolean; 
    var w:char; 
    begin
     j:=1;
     if CD.md=MSRule.md then begin
      w:=r[1];
      while l[j] in ['-','+'] do inc(j);
      packs:=copy(l,1,j-1);
     end else begin
      w:=l[1];
      while r[j] in ['-','+'] do inc(j);
      packs:=copy(r,1,j-1);
     end; 
     TestU:=(not (w in ['-','+','.'])) or (j>k);
    end;
   begin if not fail then begin
    fin:=false; i:=0; 
    if CD.md=MSRule.md then begin
     if r='*.' then begin
      if CD.s=MSRule.s then begin
       r:='0*.'; CD.p:=0;
       CD.s:=OSRule.s;
       CD.md:=1-CD.md;
       fin:=true
      end else fail:=true;
     end else Unpck0(r,Iwords);
    end else begin
     if l='b.' then begin
      if (CD.s=S_F) and (r[1]=L1wz) then begin
       l:=L1wv+'b.'; CD.p:=0;
       delete(r,1,1);
       CD.s:=S_B; CD.md:=1-CD.md;
       fin:=true
      end else fail:=true;
     end else if l<>'.' then Unpck0(l,Owords);
    end; 

    if not (fin or fail) then begin
     repeat MakeStep 
     until fail { (e_state>0) or (i>st_max) } or TestU;
     if not fail { (e_state=0) and (i<=st_max) } then begin
      if j>1 then if CD.md=MSRule.md then begin
       delete(l,1,j-1); 
       while length(packs)<k do packs:=packs+'-';
       l:=AddWord(packs,Owords,Ow_cnt)+l;
      end else begin
       delete(r,1,j-1); 
       while length(packs)<k do packs:=packs+'-';
       r:=AddWord(packs,Iwords,Iw_cnt)+r;
       if (pos('*',r)=2 + (n div k)) and (CD.s=OSRule.s)
       then begin
        packs:='';
        for j:=0 to n div k do 
         packs:=packs+Iwords[ord(r[j+1])-ord('0')];
        if packs=ocont+MSRule.c0 
         then delete(r,2,n div k);  
       end;
      end;
     end;
    end;

    {
    write(ttm,'Mc=',m,' '); wr_state(ttm,CD); flush(ttm);
    } 
   end end;

  procedure TestLemma1;
   var CD_save:TDescr; l_t:string; j:longint;
   begin if l='.' then begin
    S_F:=CD.s; L1wz:=r[1];
    CD_save:=CD;
    r:='*.'; j:=0;
    L1r1:=TD_str(CD);
    repeat SingleLoop; inc(j) until fail or (r='*.') or (j>st_max);
    if (not fail) and (r='*.') then begin
     S_B:=CD.s; L1wv:=l[1];
     L1r1:=L1r1+' --> '+TD_str(CD);
     { gotoxy(55,7); write(L1r1,'   '); }
     delete(l,1,1); l_t:=l;
     l:=L1wv+'*.'; r:=L1wz+'*.';
     L1r4:=TD_str(CD);
     repeat SingleLoop until fail or (r='*.') or (l='*.');
     if (not fail) and (r='*.') and (S_B=CD.s) and (l[1]=L1wv) then begin
      L1w0:=l[2]; L1r4:=L1r4+' --> '+TD_str(CD);
      { gotoxy(55,8); write(L1r4,'  '); }
      delete(l,1,1); r:=L1wz+'*.';
      CD.s:=S_F; CD.md:=1-CD.md;
      L1r2:=TD_str(CD);
      repeat SingleLoop until fail or (r='*.') or (l='*.');
      if (not fail) and (r='*.') and (S_B=CD.s) and (l[1]=L1wv) then begin
       L1w1:=l[2]; L1r2:=L1r2+' --> '+TD_str(CD);
       { gotoxy(55,9); write(L1r2,'  '); }
       delete(l,1,1); r:=L1wz+'*.';
       CD.s:=S_F; CD.md:=1-CD.md;
       L1r3:=TD_str(CD);
       repeat SingleLoop until fail or (r='*.') or (l='*.');
       if (not fail) and (l='*.') and (S_F=CD.s) and (r[1]=L1wz) and (r[2]=L1wz) then begin
        Lemma1:=true; L1r3:=L1r3+' --> '+TD_str(CD);
        { gotoxy(55,10); write(L1r3,' '); }
        while l_t<>'.' do begin
         if not ((l_t[1]=L1w0) or (l_t[1]=L1w1)) then Lemma1:=false;
         delete(l_t,1,1);
        end;
        if Lemma1 then begin
         gotoxy(55,5); write('L1 proved, m=',m);
        end;
       end;
      end;
     end;
    end;
    CD:=CD_save; fail:=false;
    if Lemma1 then begin l:='b.'; b_id:=BMH_cnt end;
   end end;
   
  begin
   ocont:=OSRule.a;
   oc0  :=OSRule.c0;
   k:=length(ocont); n:=length(oc0);
   repeat MakeStep until (e_state>0) or (i>st_max) or TestI;
   if TestI then begin
    BMH[BMH_cnt]:=CD; inc(BMH_cnt);
    l1:=l; l:='*.';
    repeat MakeStep until (e_state>0) or (i>st_max) or TestO;
    if TestO and (CD.s=OSRule.s) then begin
     if (GetF(r,1,k)=ocont) and (k>0) and ((n mod k)=0) then begin
      BMH[BMH_cnt]:=CD; inc(BMH_cnt);
      {
      gotoxy(55,10); write('m=',m,' n=',n,' k=',k,'  '); 
      }
      fail:=false;
      Ow_cnt:=0; Iw_cnt:=0;
      AddWord(ocont,Iwords,Iw_cnt);
      r:='0*.'; l:='';
      while (length(l1)>0) and (GetF(l1,1,n)=oc0) do delete(l1,1,n); 
      while length(l1)>1 do begin
       l:=l+AddWord(GetF(copy(l1,1,k),1,k),Owords,Ow_cnt);
       delete(l1,1,k);
      end;
      AddWord(GetF('.',1,k),Owords,Ow_cnt);
      l:=l+'.';


      write(ttm,'Owords = ');
      for j1:=0 to Ow_cnt-1 do write(ttm,Owords[j1],' ');
      writeln(ttm);
      write(ttm,'Iwords = ');
      for j1:=0 to Iw_cnt-1 do write(ttm,Iwords[j1],' ');
      writeln(ttm);

      Lemma1:=false; L1Proved:=false;
      
      repeat
       BMH[BMH_cnt]:=CD; inc(BMH_cnt);
       SingleLoop;
       if not fail then if Lemma1 
        then with BMH[b_id] do L1Proved:=
         (s=CD.s) and (md=CD.md) and
         (l=CD.l) and (r=CD.r) 
        else TestLemma1;
      until fail or L1Proved or (BMH_cnt>lim {2*lim div 3});
      {  
      for j1:=0 to Ow_cnt-1 do if j1<12 then begin
       gotoxy(70,11+j1); write(Owords[j1],' ');
       gotoxy(70,12+j1); write('      ');
      end;
      } 
      if L1Proved then e_state:=swpf_l;

     end;
    end;
   end;
  end;
 begin
  ClearDescr(CD);
  new_def:=false;
  e_state:=0; BMH_cnt:=0; i:=0;
  if MSRule.md=1 then PLoop(CD.l,CD.r) else PLoop(CD.r,CD.l);
  BMM:=CD; 
  if e_state<>swpf_l then e_state:=too_lng;
 end;

{ --------------- Exones loop/test ---------------------- }


procedure wr_ex0(var f:text);
 var i,l_b:longint;
 begin
  if Lex_cnt<26 then l_b:=EL_leter else l_b:=EL_base;
  write(f,'Left  exones:  ');
  for i:=0 to Lex_cnt-1 do write(f,chr(l_b+i),'=',Lexones[i],'  ');
  writeln(f);
  if Rex_cnt<26 then l_b:=EL_leter else l_b:=EL_base;
  write(f,'Right exones:  ');
  for i:=0 to Rex_cnt-1 do write(f,chr(l_b+i),'=',Rexones[i],'  ');
  writeln(f);
 end;
 
function Ex_str(var D:TDescr):string;
 function conv(s:string; cnt:longint):string;
  var w:string; i:byte;
  begin
   w:=s;
   if (cnt<26) and (w<>'') then for i:=1 to length(w) do 
    if ord(w[i])>=EL_base 
     then w[i]:=chr(EL_leter+ord(w[i])-EL_base);
   conv:=w;
  end;
 begin 
  with D do 
   Ex_str:=RevStr(conv(l,Lex_cnt))+SD_str(s,md)+conv(r,Rex_cnt) 
 end;

procedure wr_ex1(var f:text);
 var i:longint;
 begin
  writeln(f,'Left * consists of the expressions:  ');
  for i:=0 to Lex_cnt-1 do writeln(f,'  '+chr(EL_leter+i),'=',Lexones[i],'  ');
  writeln(f);
  writeln(f,'Right * consists of the expressions:  ');
  for i:=0 to Rex_cnt-1 do writeln(f,'  '+chr(EL_leter+i),'=',Rexones[i],'  ');
  writeln(f);
 end;

procedure SortExones(rolling:boolean);
 procedure Sort1(var exarr:TIntronArr; cnt:longint);
  var i,j,n,n0,n1:longint; s:string; w:char; succ:boolean;
  begin 
   if cnt>1 then for i:=0 to cnt-2 do for j:=i+1 to cnt-1 do
    if length(exarr[i])<length(exarr[j]) then begin
     s:=exarr[i]; exarr[i]:=exarr[j]; exarr[j]:=s
    end;

   { Roll exones to be similar to the last one } 
   if rolling then if cnt>1 
   then for j:=cnt-1 downto 1 do begin
    i:=j-1;
    s:=exarr[i]; succ:=false;
    n0:=length(exarr[j]);
    n1:=length(s)-n0;
    n:={n1} length(s);
    succ:=copy(s,n1+1,n0)=exarr[j];
    if n1>0 then while (not succ) and (n>0) do begin
     if not succ then begin w:=s[1]; delete(s,1,1); s:=s+w end;
     succ:=copy(s,n1+1,n0)=exarr[j];
     dec(n)
    end;
    if succ then exarr[i]:=s;
   end; 
  end;
 begin
  Sort1(Lexones,Lex_cnt);
  Sort1(Rexones,Rex_cnt);
 end;

const
 H_eps:byte=0;
 HuffmanMode:boolean=false;
 {
 HuffCmpMode:boolean=false;
 }
 
type 
  TExStat = array[0..bmax] of longint;
var
  T_eps:array[0..1] of longint;
  Lexstat, Rexstat:TExStat;
  LexStat1, RexStat1:TExStat;
  L_mask, R_mask:string;

procedure ClearExStats;
 var k:longint;
 begin
  for k:=0 to bmax do begin 
   LexStat[k]:=0; RexStat[k]:=0;
   LexStat1[k]:=0; RexStat1[k]:=0;
  end;
 end;

function HuffCmpStr(c0,l:string; md:byte):boolean;
 begin
  HuffCmpStr:=length(c0)+1=length(l)+T_eps[1-md]
 end;
function HuffLessStr(c0,l:string; md:byte):longint;
 begin
  HuffLessStr:=length(l)+T_eps[1-md]-length(c0)-1
 end;
 
function MakeEStep(var DF:TDescr):byte;
 var simple:boolean; 

 function OldVertex(var CTG:TGraph; CTG_cnt:longint):boolean;
  var j:longint; 
  begin
   OldVertex:=false;
   for j:=0 to CTG_cnt-1 do if SimMacro2(DF,CTG[j].D)
    then OldVertex:=true;
  end;
 procedure AddVertex(var CTG:TGraph; var CTG_cnt:longint);
  begin
   if not OldVertex(CTG,CTG_cnt) then if CTG_cnt<gfin_max then begin
    CTG[CTG_cnt].D:=DF;
    CTG[CTG_cnt].checked:=false;
    inc(CTG_cnt);
   end else begin
    e_state:=too_lng;
    pr_fail:=true;
   end; 
  end;

 procedure MakeELoopStep;
  procedure Test(
    var l,r:string; 
    var Lexs, Rexs:TIntronArr; 
    var L_cnt,R_cnt:longint;
    var ExStat,ExStat1:TExStat);
   procedure Pack_l;
    var 
     j,n:longint; c0a,c0b,l1,l2:string; 
     w:char; succ,repack:boolean;
    begin
     repack:=false; n:=Pos('[',l);
     if n>1 then begin
      w:=l[n+1];
      for j:=0 to L_cnt-1 do begin
       c0b:=Lexs[j];
       
       if HuffmanMode and (l[n+2]=']') then begin
        l2:=l; delete(l2,1,n+2);
        l1:=copy(l,1,n-1)+Lexs[ord(w)-EL_base]+l2;
        c0a:=GetF(l1,1,length(c0b));
        if (c0a=c0b) and HuffCmpStr(c0b,l1,DF.md) then begin
         repack:=true;
         l:='['+chr(EL_base+j)+']'+l2;
        end; 
       end else begin
        c0a:=copy(l,1,n-1)+Lexs[ord(w)-EL_base];
        if c0a=c0b then begin
         repack:=true; 
         delete(l,1,n+1);
         l:='['+chr(EL_base+j)+l;
        end;
       end;
       
      end;
     end;
     if not repack then for j:=0 to L_cnt-1 do begin
      c0b:=Lexs[j];
      c0a:=GetF(l,1,length(c0b));
      succ:=c0a=c0b;
      
      if HuffmanMode then if succ 
       then begin
        if Pos('[',l)=length(c0b)+1
         then succ:=true
         else if Pos('[',l)>0
          then succ:=false
          else succ:=HuffCmpStr(c0b,l,DF.md)
       end;
      
      if succ then begin 
       if DF.af then simple:=false;
       delete(l,1,length(c0a));
       if l='' then l:='.';
       if Pos('[',l)=1 
        then delete(l,1,1) 
        else begin
         if (l<>'.') and (not HuffmanMode) then Pack_l;
         if Pos('[',l)=1  
          then delete(l,1,1)
          else IncS(']',l,DF.af);
        end; 
       w:=chr(EL_base+j); 

       if not DF.af then begin
        if Pos(']',l)>1 then begin
         inc(ExStat[ord(l[1])-EL_base]);
        end; 
        if Pos(']',l)>2{3} then begin
         inc(ExStat1[ord(l[1{2}])-EL_base]);
        end; 
       end;

       IncS('['+w,l,DF.af);
      end;
      { bad attempt to resolve SemiHuffman repacking }
      { 
      else begin
       if HuffmanMode and (l[1] in ['+','-']) then begin
        w:=l[1]; delete(l,1,1);   
        Pack_l; l:=w+l;
       end;
      end;
      }
     end; 
    end;
   procedure TestIO;
    var nw,ow:string; i:word;
    function NoShorter:boolean;
     var j:word;
     begin
      NoShorter:=true;
      if i<R_cnt-1 then begin
       nw:=ow; delete(nw,1,1);
       for j:=i+1 to R_cnt-1 do 
        if Rexs[j]=nw then begin
         NoShorter:=false;
         r[2]:=chr(EL_base+j);
         r:=ow[1]+r;
        end;
      end;
     end;
    begin 
     if Pos('[',r)=1 then begin
      i:=ord(r[2])-EL_base;
      ow:=Rexs[i];
      if NoShorter then begin
       delete(r,1,2);
       if r[1]=']' then delete(r,1,1) else r:='['+r;
       IncS(ow,r,DF.af);
       simple:=false;
      end;
     end;
    end; 
   procedure Pack_l_Rec;
    var c0b:string; k,j:longint;
    begin
     for j:=0 to L_cnt-1 do if Pos('[',l)=0 then begin
      c0b:=Lexs[j];
      k:=HuffLessStr(c0b,l,DF.md);
      if k>0 then begin
       c0b:=copy(l,1,k);
       delete(l,1,k);
       Pack_l;
       l:=c0b+l;
      end; 
     end;
     Pack_l;    
    end;
   var l_save:string; md_o,nl:byte; 
   begin 
    nl:=Pos('[',l);
    if (nl>H_eps) or ((nl=0) and (length(l)>H_eps)) then begin
     l_save:=copy(l,1,H_eps); delete(l,1,H_eps);
     Pack_l_Rec; l:=l_save+l;
    end;
    { Pack_l; }
    TestIO;
    md_o:=DF.md;
    if simple then MakeMStep0(DF,0);  
    if (r='.') and (DF.md=md_o) then begin
     simple:=false;
     {
     with DF do if md=1
      then l_mark:=RevStr(l)+SD_str(s,md)+r
      else r_mark:=RevStr(l)+SD_str(s,md)+r;
     } 
    end; 
   end;
  begin
   {
   with DF do begin
    writeln(ttm,'ELoopStep --> ',RevStr(l)+SD_str(s,md)+r);
    flush(ttm);
   end;
   }
   if DF.md=1 
    then Test(DF.l,DF.r,Lexones,Rexones,Lex_cnt,Rex_cnt,LexStat,LexStat1)
    else Test(DF.r,DF.l,Rexones,Lexones,Rex_cnt,Lex_cnt,RexStat,RexStat1);
  end;
  
 begin
  pr_fail:=false;
  
  with DF do begin rname0:='   '; rname1:='   ' end;
  BBGs_cnt:=1; BBGs[0].D:=DF;   
  simple:=true; 
  repeat
   MakeELoopStep;
   { if not pr_fail then }
   if simple then if OldVertex(BBGs,BBGs_cnt)
    then begin e_state:=b_loop; pr_fail:=true end
    else AddVertex(BBGs,BBGs_cnt);
  until (not simple) or (e_state>0) or pr_fail;

  if pr_fail and DF.af
   then MakeEStep:=mem_ov
   else MakeEStep:=e_state;
 end;

procedure MacroLoop(
 var CD:TDescr; var MH:THistory; var MH_cnt:longint; 
 mmode:byte; lim:longint); forward;

{ -------- Exone Grammar test: --------- }

var
 MidArr:array[byte] of string;
 Mid_cnt:byte;

procedure GenMidStr_0(lc:char; mid:string);
 var patt,tail:string; n0:byte;
 begin
  Mid_cnt:=0;
  n0:=Pos('}',mid);
  tail:=mid; delete(tail,1,n0);
  patt:=copy(mid,2,n0-2);
  while length(patt)>0 do begin
   if patt[1]=lc then begin
    if length(patt)=2
     then MidArr[Mid_cnt]:=lc+patt[2]+tail
     else MidArr[Mid_cnt]:=lc+patt[2]+mid;
    inc(Mid_cnt); 
   end;  
   if Pos(',',patt)>0
    then delete(patt,1,3) 
    else patt:='';
  end;
 end;

procedure GenMidStr_1(mid:string);
 var tail:string; n0,i:byte;
 begin
  Mid_cnt:=0;
  n0:=Pos('}',mid);
  tail:=mid; delete(tail,1,n0);
  for i:=2 to n0-1 do begin
   MidArr[Mid_cnt]:=mid[i]+mid;
   inc(Mid_cnt);  
   MidArr[Mid_cnt]:=mid[i]+tail;
   inc(Mid_cnt);
  end;
 end;

function PackG_0(mid:string; var packOK:boolean; ex_cnt:word):string;
 var n0,n1:byte; 

 function InsPatt(tup,patt:string):string;
  var p0,p1,t1,exused:string; n0:byte; found:boolean;
  function ManyExones:boolean;
   var i,n:byte;
   begin
    n:=0;
    for i:=1 to ex_cnt do if exused[i]='*' then inc(n);
    ManyExones:=(ex_cnt>5 {4 ?}) and (5*n>4*ex_cnt) {3/2;4/3;5/4};    
   end;
  begin
   exused:=''; for n0:=1 to ex_cnt do exused:=exused+' ';
   (* Example: tup=bb patt={ab,bc,bb} *) 
   p0:=patt; n0:=length(p0);
   p1:=copy(p0,n0-2,3); delete(p0,n0-3,4);
   (* p1=bb} p0={ab,bc *)
   exused[1+ord(p1[1])-EL_base]:='*';
   exused[1+ord(tup[1])-EL_base]:='*';
   
   found:=false;
   while length(p0)>0 do begin
    n0:=length(p0);
    t1:=copy(p0,n0-1,2); 
    delete(p0,n0-2,3);
    if (t1<=tup) and (not found) then begin 
     found:=true;
     if t1<tup then p1:=tup+','+p1;
    end;
    p1:=t1+','+p1;
    exused[1+ord(p1[1])-EL_base]:='*';
   end;
   if found 
    then p1:='{'+p1
    else p1:='{'+tup+','+p1;

   if length(p1)>220 then pr_fail:=true;
   if ManyExones {(Pos(' ',exused)=0) or (ex_cnt>9)} 
    then pr_fail:=true;
   InsPatt:=p1;  
  end;
  
 begin
  PackG_0:=mid;
  packOK:=true;

  n0:=length(mid);
  n1:=Pos('{',mid);
  if n1>0 then begin
   packOK:=n1<=3; 
   if n1>=3 then PackG_0:=
    copy(mid,1,n1-2)+
    InsPatt(
     copy(mid,n1-2,2),
     copy(mid,n1,n0-n1+1));
  end else begin
   PackG_0:=copy(mid,1,n0-1)+'{'+copy(mid,n0-1,2)+'}';
   packOK:=n0=2;
  end;
 end;

function PackG_1(mid:string; var packOK:boolean):string;
 var n0,n1:byte; 

 function InsPatt(nc:char; patt:string):string;
  var p0,tail:string; n0:byte; found:boolean;
  begin
   (* Example: nc=b patt={abd}x *) 
   n0:=Pos('}',patt);
   tail:=patt; delete(tail,1,n0-1);
   p0:=patt; delete(p0,n0,length(p0)-n0+1);
   (* tail=}x p0={abd *)
   
   found:=false;
   n0:=length(p0);
   while n0>1 do begin
    if (p0[n0]<=nc) and (not found) then begin 
     found:=true;
     if p0[n0]<nc then tail:=nc+tail;
    end;
    tail:=p0[n0]+tail;
    dec(n0);
   end;
   if found 
    then tail:='{'+tail
    else tail:='{'+nc+tail;

   if length(tail)>220 then pr_fail:=true;
   InsPatt:=tail;  
  end;
  
 begin
  PackG_1:=mid; packOK:=true;

  n0:=length(mid); { must be >=2 !!! }
  n1:=Pos('{',mid);
  if n1>0 then begin
   packOK:=n1<=2; 
   if n1>=2 then PackG_1:=
    copy(mid,1,n1-2)+
    InsPatt(mid[n1-1],copy(mid,n1,n0-n1+1));
  end else begin
   PackG_1:=copy(mid,1,n0-2)+'{'+mid[n0-1]+'}'+mid[n0];
   packOK:=n0=2;
  end;
 end;

function PackG_2(mid:string; var packOK:boolean; ex_cnt:word):string;
 var 
  ExCnts:array[byte] of longint;
  mid_u:string;

 procedure ExStat_0;
  var i,k:byte; bmod:boolean;
  begin
   for i:=0 to ex_cnt-1 do ExCnts[i]:=0;
   bmod:=false;
   for i:=1 to length(mid) do if mid[i] in ['{','}']
    then bmod:=not bmod
    else begin
     if bmod then k:=2 else k:=1;
     inc(ExCnts[ord(mid[i])-EL_base],k);
    end; 
   mid_u:=mid;
   for i:=1 to length(mid) do
    if mid[i] in ['{','}']
     then mid_u[i]:=' '
     else if ExCnts[ord(mid[i])-EL_base]=1
      then mid_u[i]:='u' else mid_u[i]:=' '; 
  end;

 function Pack(s:string):string;
  var 
   Exones:array[byte] of boolean;
   res:string; i:byte;
  begin
   {writeln(ttm,'Pack -->   s="',s,'"'); flush(ttm);}
   for i:=0 to ex_cnt-1 do Exones[i]:=false;
   for i:=1 to length(s) do 
    if not (s[i] in ['{','}']) 
     then Exones[ord(s[i])-EL_base]:=true;
   res:='{';
   for i:=0 to ex_cnt-1 do if Exones[i]
    then res:=res+chr(i+EL_base);
   Pack:=res+'}';
  end;

 function RecPack(m_u,m_s:string):string;
  var n0,n1,n2:byte;
  begin
   {
   writeln(ttm,'RecPack -->  m_u="',m_u,'"  m_s=',m_s); 
   flush(ttm);
   }
   n1:=length(m_s);
   if n1=0 then RecPack:='' else begin
    n0:=Pos('u',m_u);
    if n0>1
     then RecPack:=
      Pack(copy(m_s,1,n0-1))+m_s[n0]+
      RecPack(copy(m_u,n0+1,n1-n0),
              copy(m_s,n0+1,n1-n0))
     else if n0=1 then begin
      n2:=Pos(' ',m_u);
      if n2>0 
       then RecPack:=copy(m_s,1,n2-1)+
            RecPack(copy(m_u,n2,n1-n2+1),
                    copy(m_s,n2,n1-n2+1))
       else RecPack:=m_s;             
     end else RecPack:=Pack(m_s);
   end;
  end;

 var res:string;
 begin
  packOK:=true;
  ExStat_0;
  res:=RecPack(mid_u,mid);

  {
  write(ttm,' mid=',mid);
  write(ttm,' mid_u=',mid_u);
  writeln(ttm,' pack=',res);
  flush(ttm); 
  }
  
  if length(res)>200 then pr_fail:=true;
  PackG_2:=res;
 end;

function IncludeG_0(var D1,D2:TDescr):boolean;
 function IncStr(l0,l1:string):boolean;
  var n0,n1,k0,k1:byte; h0,h1:string;
  function Include0:boolean;
   var n0,n1:byte; succ:boolean; t0,t1:string;
   begin
    n0:=length(h0); n1:=length(h1);
    if copy(h0,n0-1,2)=copy(h1,n1-1,2) then begin 
     delete(h0,n0-2,3);
     delete(h1,n1-2,3);
     succ:=true;
     while succ and (length(h1)>0) do begin
      n0:=length(h0); n1:=length(h1);
      if n0<n1 then succ:=false else begin
       t0:=copy(h0,n0-1,2); t1:=copy(h1,n1-1,2);
       if t0<t1 then succ:=false else begin
        delete(h0,n0-2,3);
        if t0=t1 then delete(h1,n1-2,3);
       end;
      end;      
     end;
     Include0:=succ;
    end else Include0:=false;
   end;
  begin
   if l0=l1 then IncStr:=true else begin
    n0:=Pos('{',l0);
    n1:=Pos('{',l1);
    if (n0>0) and (n0=n1) then begin
     k0:=Pos('}',l0);
     k1:=Pos('}',l1);
     h0:=copy(l0,k0,length(l0)+1-k0);
     h1:=copy(l1,k1,length(l1)+1-k1);
     if (copy(l0,1,n0)=copy(l1,1,n1)) and
        (h0=h1) then begin
      h0:=copy(l0,n0,k0-n0);
      h1:=copy(l1,n1,k1-n1);
      IncStr:=Include0;
     end else IncStr:=false;   
    end else IncStr:=false;
   end;
  end; 
 begin
  IncludeG_0:=
   IncStr(D1.l,D2.l) and IncStr(D1.r,D2.r)
   and (D1.s=D2.s) and (D1.md=D2.md);
 end;

function IncludeG_1(var D1,D2:TDescr):boolean;
 function IncStr(l0,l1:string):boolean;
  var n0,n1,k0,k1:byte; h0,h1:string;
  function Include0:boolean;
   var n0,n1:byte; succ:boolean; 
   begin
    succ:=true; n0:=length(h0); n1:=length(h1);
    while succ and (n1>0) do begin
     if n0<n1 then succ:=false else begin
      if h0[n0]<h1[n1] 
       then succ:=false 
       else begin dec(n0); if h0[n0]=h1[n1] then dec(n1) end;
     end;      
    end;
    Include0:=succ;
   end;
  begin
   if l0=l1 then IncStr:=true else begin
    n0:=Pos('{',l0);
    n1:=Pos('{',l1);
    if (n0>0) and (n0=n1) then begin
     k0:=Pos('}',l0);
     k1:=Pos('}',l1);
     h0:=copy(l0,k0,length(l0)+1-k0);
     h1:=copy(l1,k1,length(l1)+1-k1);
     if (copy(l0,1,n0)=copy(l1,1,n1)) and
        (h0=h1) then begin
      h0:=copy(l0,n0+1,k0-n0-1);
      h1:=copy(l1,n1+1,k1-n1-1);
      IncStr:=Include0;
     end else IncStr:=false;   
    end else IncStr:=false;
   end;
  end; 
 begin
  IncludeG_1:=
   IncStr(D1.l,D2.l) and IncStr(D1.r,D2.r)
   and (D1.s=D2.s) and (D1.md=D2.md);
 end;

function PosL(c:char; s:string):byte;
 var i,n:byte;
 begin
  n:=Pos(c,s);
  if n>0 then begin
   for i:=n to length(s) do 
    if s[i]=c then PosL:=i;
  end else PosL:=n;
 end;
 
function IncludeG_2(var D1,D2:TDescr):boolean;
 function IncStr(l0,l1:string):boolean;
  var n0,n1,k0,k1,i:byte; h0,h1,t0,t1:string;
  function Include0(h0,h1:string):boolean;
   var n0,n1:byte; succ:boolean; 
   begin
    succ:=true; 
    n0:=length(h0); n1:=length(h1);
    while succ and (n1>0) do begin
     if n0<n1 then succ:=false else begin
      if h0[n0]<h1[n1] 
       then succ:=false 
       else begin dec(n0); if h0[n0]=h1[n1] then dec(n1) end;
     end;      
    end;
    Include0:=succ;
   end;
  begin
   if l0=l1 then IncStr:=true else begin
    n0:=Pos('{',l0);
    n1:=Pos('{',l1);
    if (n0>0) and (n0=n1) then begin
     k0:=PosL('}',l0);
     k1:=PosL('}',l1);
     h0:=copy(l0,k0,length(l0)+1-k0);
     h1:=copy(l1,k1,length(l1)+1-k1);
     if (copy(l0,1,n0)=copy(l1,1,n1)) and
        (h0=h1) then begin
      h0:=copy(l0,n0+1,k0-n0-1);
      h1:=copy(l1,n1+1,k1-n1-1);
      k0:=Pos('}',h0);
      k1:=Pos('}',h1);
      if (k0=0) and (k1=0)
       then IncStr:=Include0(h0,h1)
       else if (k0>0) and (k1>0) then begin
        n0:=Pos('{',h0);
        n1:=Pos('{',h1);
        t0:=h0; delete(t0,1,n0);
        t1:=h1; delete(t1,1,n1);
        if (Pos('{',t0)=0) and (Pos('{',t1)=0)
         then IncStr:=
          Include0(t0,t1) and
          Include0(copy(h0,1,k0-1),copy(h1,1,k1-1)) and
          (copy(h0,k0,n0-k0)=copy(h1,k1,n1-k1))
         else IncStr:=false;
       end else if (k0=0) and (k1>0) then begin
        IncStr:=true;
        for i:=1 to length(h1) do        
         if not (h1[i] in ['{','}']) 
          then if Pos(h1[i],h0)=0 
           then IncStr:=false; 
       end else IncStr:=false;
     end else IncStr:=false;   
    end else IncStr:=false;
   end;
  end; 
 begin
  IncludeG_2:=
   IncStr(D1.l,D2.l) and IncStr(D1.r,D2.r)
   and (D1.s=D2.s) and (D1.md=D2.md);
 end;
 
function IncludeG(var D1,D2:TDescr; gram_mod:byte):boolean;
 begin case gram_mod of
  0:IncludeG:=IncludeG_0(D1,D2);
  1:IncludeG:=IncludeG_1(D1,D2);
  2:IncludeG:=IncludeG_2(D1,D2) {false};
 end end;
function PackG(
 mid:string; var packOK:boolean; gram_mod:byte; l_cnt:word):string;
 begin case gram_mod of
  0:packG:=PackG_0(mid,packOK,l_cnt);
  1:packG:=PackG_1(mid,packOK);
  2:packG:=PackG_2(mid,packOK,l_cnt);
 end end;
 
procedure TryExGFin(g_max:longint; gram_mod:byte);
 const av_max=800;
 var
  old_gcnt, i_0,i_1:longint; 
  closed, simple:boolean;
  DF:TDescr;
  BBG1:TGraph;
  BBG1_cnt:longint;
  AvNodes:array[0..av_max] of longint;
  Av_cnt:longint;

 function Av_found(i0:longint):boolean;
  var i:longint;
  begin
   Av_found:=false;
   if Av_cnt>0 then for i:=0 to Av_Cnt-1 do
    if i0=AvNodes[i] then Av_found:=true;
  end;
 procedure Add_Av(j:longint);
  {var found:boolean; i:longint;}
  begin if Av_cnt<av_max then begin
   {
   found:=false;
   if Av_cnt>0 then for i:=0 to Av_Cnt-1 do
    if j=AvNodes[i] then found:=true;
   if not found then begin
   } 
   if not Av_found(j) then begin
    AvNodes[Av_cnt]:=j;
    inc(Av_cnt);
    if Av_cnt mod 10 = 0 then begin
     gotoxy(55,10);
     write('G/A/m=',BBG_cnt:4,'/',Av_cnt:3,'/',gram_mod);
    end;
   end;
  end end;

 function OldVertex(var CTG:TGraph; CTG_cnt:longint):boolean;
  var j:longint; 
  begin
   OldVertex:=false;
   for j:=0 to CTG_cnt-1 do if SimMacro2(DF,CTG[j].D)
    then OldVertex:=true;
  end;
 procedure AddVertex(var CTG:TGraph; var CTG_cnt:longint);
  begin
   if not OldVertex(CTG,CTG_cnt) then if CTG_cnt<g_max then begin
    CTG[CTG_cnt].D:=DF;
    CTG[CTG_cnt].checked:=false;
    inc(CTG_cnt);
   end else pr_fail:=true;
  end;
  
 function OldIVertex(var CTG:TGraph; CTG_cnt:longint):boolean;
  var j:longint; 
  begin
   OldIVertex:=false;
   for j:=0 to CTG_cnt-1 do if SimMacro2(DF,CTG[j].D)
    then OldIVertex:=true
    else if IncludeG(CTG[j].D,DF,gram_mod)
     then OldIVertex:=true
     else if IncludeG(DF,CTG[j].D,gram_mod) then begin
      CTG[j].checked:=true;
      if j<>i_1 then Add_Av(j);
     end;
  end;
 procedure AddIVertex(var CTG:TGraph; var CTG_cnt:longint);
  var id{,i}:longint;
  begin
   if not OldIVertex(CTG,CTG_cnt) then if CTG_cnt<g_max then begin
    if Av_cnt>0 then begin
     dec(Av_cnt); id:=AvNodes[Av_cnt];
    end else begin
     id:=CTG_cnt; inc(CTG_cnt);
    end;
    CTG[id].D:=DF;
    CTG[id].checked:=false;
    if id<i_0 then i_0:=id;
   end else if not pr_fail then begin
    if {true} g_max>=(gfin_max*2) then begin
     write(ttm,'m=',m,' g_max/i_0=',g_max,'/',i_0,' '); 
     write(ttm,'gram=',gram_mod,' H/T=',H_eps,'/',T_eps[0],'|',T_eps[1]);
     writeln(ttm,' S/H=',LR_mod,' i/j=',Lex_id,'-',Rex_id);
     { 
     ClearExStats;
     MacroLoop(CEM,EMH,EMH_cnt,4,2*dump_max);
     wr_exones(ttm);
     }
     {
     wr_ex0(ttm);
     for i:=0 to g_max-1 do if not Av_found(i) then begin
      with CTG[i].D do write(ttm,RevStr(l)+SD_Str(s,md)+r);
      if CTG[i].checked then write(ttm,' Checked');
      writeln(ttm,' i=',i);
     end; 
     }
     flush(ttm);
    end;
    pr_fail:=true;
   end; 
  end;
  
 procedure Test(var l,r:string; l_cnt:word);
  var n0,n1:byte;

  procedure Pack;
   var tail,mid,head:string; packOK:boolean;
   begin
    repeat
     packOK:=true;
     n0:=Pos('[',l); n1:=Pos(']',l);
     if n0>0 then 
     if n1-n0>=4 then begin
      tail:=l; delete(tail,1,n1-1);
      head:=copy(l,1,n0+1);
      mid :=copy(l,n0+2,n1-n0-2);
      l:=head+PackG(mid,packOK,gram_mod,l_cnt)+tail;
     end;
    until packOK; 
   end;

  procedure Unpack;
   var n2,k:byte; tail,mid,head:string;  
   function NeedWord:boolean;
    begin case gram_mod of
     0:NeedWord:=n1=n0+2;
     1,2:NeedWord:=n1=n0+1;
    end end;
   procedure GenMidStr;
    var lc:char;
    begin case gram_mod of
     0:begin lc:=r[n0+1]; GenMidStr_0(lc,mid) end;
     1,2:GenMidStr_1(mid);
     { 2:GenMidStr_1(mid); } 
    end end;
   begin
    n0:=Pos('[',r); n1:=Pos('{',r); n2:=Pos(']',r);
    if n1>0 then begin
     if NeedWord {n1-n0=2} then begin
      tail:=r; delete(tail,1,n2-1);
      head:=copy(r,1,n0);
      mid :=copy(r,n1,n2-n1);
      GenMidStr;

      if Mid_cnt=0 then begin
       writeln(ttm,'Error: empthy Grammar !');
       flush(ttm); Halt;
      end;

      if Mid_cnt>1 then begin
       simple:=false;
       for k:=0 to Mid_cnt-1 do begin
        r:=head+MidArr[k]+tail;     
        AddIVertex(BBG,BBG_cnt); 
       end;
      end else r:=head+MidArr[0]+tail; 
      
     end;
    end; 
   end;
  
  begin
   Pack;
   Unpack;
  end;

 procedure Loop;
  var state:byte;
  begin
   simple:=true;
   BBG1_cnt:=1; BBG1[0].D:=DF;
   repeat
    state:=MakeEStep(DF);

    {        
    writeln(ttm,'BBG1_cnt=',BBG1_cnt,'  ',
           '-->  ',RevStr(DF.l),SD_str(DF.s,DF.md),DF.r);
    flush(ttm);
    }
    
    if state=0 then begin
     BBG[i_1].checked:=true;
     BBG[i_1].DNext:=DF;
     if DF.md=1 
      then Test(DF.l,DF.r,Lex_cnt)
      else Test(DF.r,DF.l,Rex_cnt);

     if simple then if OldVertex(BBG1,BBG1_cnt)
      then begin
       simple:=false;
       AddIVertex(BBG,BBG_cnt);
      end else AddVertex(BBG1,BBG1_cnt);
      
    end else pr_fail:=true;
   until (not simple) or pr_fail; 
  end;

 begin

  if g_max>2*gfin_max then begin
   gotoxy(1,24); 
   writeln('Error: g_max must be less than ',2*gfin_max,' !');
   Halt;
  end;

  old_gcnt:=0;
  ClearExStats;

  repeat
   BBG_cnt:=1; i_0:=0;
   Av_cnt:=0;
   pr_fail:=false;
   ClearExStats;
   
   ClearDescr(DF);
   pr_fail:=false;
   
    e_state:=0;
    DF.af:=true; { ??? } 
    with BBG[0] do begin D:=DF; checked:=false end;
   
    while (not pr_fail) and (i_0<BBG_cnt) do begin
     DF:=BBG[i_0].D; 
     i_1:=i_0; inc(i_0);
     if not BBG[i_1].checked then Loop; 
    end;
   
    closed:=BBG_cnt=old_gcnt;
    
    if not closed then old_gcnt:=BBG_cnt;
  until pr_fail or closed;

  if not pr_fail then begin
   
   ClearExStats;
   MacroLoop(CEM,EMH,EMH_cnt,4,dump_max);
   {   
   writeln(ttm,'M=',m,' TryExGFin prooof succeed !!!  g_fin=',BBG_cnt); 
   wr_grapf(ttm,BBG,BBG_cnt); 
   wr_exones(ttm);
   flush(ttm); 
   }
   e_state:=exS2_l;
  end else begin
   { writeln(ttm,'M=',m,' TryExGFin prooof fail !!!'); }

   {
   if (g_max<gfin_max) and (T_eps[0]=0) and (T_eps[1]=0) and
      (Lex_cnt>2) and (Rex_cnt>2) 
   then begin
    ClearExStats;
    MacroLoop(CEM,EMH,EMH_cnt,4,2*dump_max);
    wr_exones(ttm);
    flush(ttm);
   end;
   }

   e_state:=0; 
  end; 

 end;

{ ----------------------------------------------------------- }

procedure CollatzLoop(
 var CD:TDescr; var MH:THistory; 
 var MH_cnt:longint; lim:longint);
 const max_cnt=100000000; 
 var vc0:longint;
 begin
  ClearDescr(CD);
  MH_cnt:=0;
  new_def:=false;
  e_state:=0;
  repeat
   vc0:=VarCount(CD);
   MH[MH_cnt]:=CD; inc(MH_cnt); 

   {writeln(ttm);}

   repeat
    MakeMStep0(CD,1);
    {
    with CD do writeln(ttm,'c:',c,' ',RevStr(l),SD_str(s,md),r,
     '  e_state=',e_state,' vc=',VarCount(CD));
    flush(ttm); 
    }
   until 
    (VarCount(CD)<>vc0) or (CD.s=0) or
    (e_state>0) or (CD.c>max_cnt);   

   if MH_cnt mod 10=0 then begin
    gotoxy(55,2); write('Collatz_cnt=',MH_cnt,' ');
   end;

   if CD.c>max_cnt then begin
       CM:=Cl_M;
       MH:=ClMH;
       MH_cnt:=ClMH_cnt;
      { 
       writeln(ttm,'------- Collatz-like bad machine: ------');
       writeln(ttm,'M# = ',m-1); 
       wrf_m(ttm,true,false);
       wr_rules(ttm,'approved shift',SRules,SR_cnt,false);
       wr_mhistory(ttm,cmax);
       wr_grapf(ttm,CTG,CTG_cnt,false);
       writeln(ttm,'-------------------------------------');
      } 
       e_state:=too_lng;
   end;

   if CD.s=0 then e_state:=col0_e;
   if MH_cnt>=lim then e_state:=too_lng;
   if new_def and (e_state=0) then begin
    InvSTest;
    if (e_state=0) and lDum then back_track;
    new_def:=false;
   end;
  until e_state>0;

  { If fail, continue normal interpretation }
  if e_state<>col0_e then e_state:=0;
  
 end;

procedure MacroLoop(
 var CD:TDescr; var MH:THistory; var MH_cnt:longint; 
 mmode:byte; lim:longint);

 procedure Make100Steps;
  var i:longint;
  begin
   i:=0;
   repeat
    MakeMStep0(CD,0);
    inc(i);
   until (i=100) or new_def or (e_state>0); 
  end;
  
 begin
  gfin_lim:=lim;
  ClearDescr(CD);
  MH_cnt:=0;
  new_def:=false;
  e_state:=0;
  repeat
   MH[MH_cnt]:=CD; inc(MH_cnt); 
   case mmode of
    1:MakeMStep(CD);
    2:MakeMStep0(CD,2);
    3:MakeBStep(CD);
    4:MakeEStep(CD);
    5:MakeMStep0(CD,3);
    6:Make100Steps;
   end; 
   
   if MH_cnt mod 100=0 then begin
    gotoxy(55,6); write('MH_cnt=',MH_cnt,' ');
   end;

   if MH_cnt>=lim then e_state:=too_lng;
   if new_def and (e_state=0) then begin
    InvSTest;
    if (e_state=0) and lDum then back_track;
    new_def:=false;
   end;
  until e_state>0;

  { PackPatt tuning }
  { 
  if (mmode=1) and (rule_min=5) then begin
   wr_rules(ttm,'approved shift',SRules,SR_cnt,false);
   wr_mhistory(ttm,lim);
   flush(ttm);
  end;
  }

 end;

(*
procedure CreateOSRules;
 var i,j,k:longint; TR:TRule; succ:boolean; w:char;
 begin 
  OSR_cnt:=0; OSR_main:=-1;
  with MainRule do for i:=0 to ASR_cnt-1 
  do if md<>ASRules[i].md then for j:=0 to Patt_cnt-1
  do if (ASRules[i].c0=Patts[j].c1) then begin
   TR:=ASRules[i]; succ:=false;
   for k:=0 to length(TR.c1)-1 do if not succ then begin
    if TR.c1=Patts[j].c0 then begin
     OSRules[OSR_cnt]:=TR;
     if j=m_id then OSR_main:=OSR_cnt;
     inc(OSR_cnt); succ:=true;
    end else with TR do begin
     w:=c1[1]; delete(c1,1,1);
     c1:=c1+w; a:=a+w;
    end;
   end;
  end;
  if OSR_main>=0 then OSRule:=OSRules[OSR_main];
  OSRule.p:=(OSRule.md+OSRule.md-1)*length(OSRule.c0);
 end;
*)

procedure wr_exones(var f:text); 
 var i,lim:longint;
 begin
  wr_ex0(f);
  EMH[EMH_cnt]:=CEM; 
  lim:=EMH_cnt {dump_max} ;
  if lim>EMH_cnt then lim:=EMH_cnt;
  writeln(f);
  writeln(f,'First ',lim,' exone macro stEps:');
  writeln(f,' ind      p         c             LsdR');
  for i:=0 to lim do with EMH[i] do begin
   write(f,i:4,' ',p:6,c:10,':  ');
   writeln(f,Ex_str(EMH[i]));
  end; 
  writeln(f);
 end;

procedure DoubleExones(
 var Exones:TIntronArr; var Ex_cnt:longint);
 var i,l:longint;
 begin 
  l:=Ex_cnt;
  if l<=32 then for i:=0 to l-1 do begin 
    Exones[Ex_cnt]:='-'+Exones[i];
    Exones[i]     :='+'+Exones[i];
    inc(Ex_cnt);
  end; 
 end;

procedure SqrExones(
 var Exones:TIntronArr; var Ex_cnt:longint);
 var i,j,l:longint;
 begin 
  l:=Ex_cnt;
  if l<=8 then begin
   for i:=0 to l-1 do for j:=0 to l-1 do 
   if i<>j then begin
    Exones[Ex_cnt]:=Exones[i]+Exones[j];
    inc(Ex_cnt);
   end;
   for i:=0 to l-1 do
    Exones[i]:=Exones[i]+Exones[i];
  end; 
 end;

const
 Huff_size = 9;
 HStat_max = 1000;
type
 HStatEl=record
   mode,eps,i,j,cnt:longint;
  end;
 HuffCodesArr = array[0..ESet_max] of TExoneSet;
 
var 
 HuffCodes: HuffCodesArr; Huff_cnt:longint;
 SemiCodes: HuffCodesArr; Semi_cnt:longint;
 
 H_Stats: array[0..HStat_max] of HStatEl;
 H_St_cnt:longint;

function GetHStat0(amode,eps0,i0:longint):boolean;
 var found:boolean; k:longint;
 begin
  found:=false;
  if H_St_cnt>0 then for k:=0 to H_St_cnt-1 do
   with H_Stats[k] do if 
    (mode=amode) and (eps=eps0) and ((i=i0) or (j=i0)) 
    then found:=true;
  GetHStat0:=found;
 end;
 
function GetHStat(amode,eps,i,j:longint; proved:boolean):boolean;
 var 
  f:text;
  S0:HStatEl; found:boolean; k:longint;
 begin
  S0.mode:=amode;
  S0.eps:=eps; S0.cnt:=1;
  if i>j then begin
   S0.i:=j; S0.j:=i;
  end else begin
   S0.i:=i; S0.j:=j;
  end;
  found:=false;
  if H_St_cnt>0 then for k:=0 to H_St_cnt-1 do
   with H_Stats[k] do if 
    (mode=S0.mode) and (eps=S0.eps) and (i=S0.i) and (j=S0.j) 
    then begin found:=true; if proved then inc(cnt) end;
  if (not found) and (H_St_cnt<HStat_max) and proved then begin
   H_Stats[H_St_cnt]:=S0;
   inc(H_St_cnt);
   if H_St_cnt>0 then begin
    assign(f,'HuffStat.txt');
    rewrite(f);
    for k:=0 to H_St_cnt-1 do with H_Stats[k] do
     writeln(f,mode,' ',eps,' ',i,' ',j,' ',cnt);
    close(f);
   end;
  end;
  GetHStat:=found;
 end;
 
procedure InitHStat;
 var f:text; w:string; mode,eps,i,j:longint;
 function GetInt:longint;
  var w1:string; i,n:longint;
  begin
   w1:=copy(w,1,Pos(' ',w)-1);
   val(w1,n,i);
   delete(w,1,Pos(' ',w));
   GetInt:=n;
  end;
 begin
  H_St_cnt:=0;
  {$I-} assign(f,'HuffStat.dat'); reset(f); {$I+}
  if IOResult=0 then while not eof(f) do begin
   readln(f,w); 
   mode:=GetInt; eps:=GetInt; 
   i:=GetInt; j:=GetInt;
   GetHStat(mode,eps,i,j,true);  
  end;
 end;
 
procedure SortHSet(var G0:TExoneSet);
 var i,j:longint; w:string;
 function Less(s1,s2:string):boolean;
  begin
   if length(s1)<>length(s2) 
    then Less:=length(s1)<length(s2)
    else Less:=RevStr(s1)>RevStr(s2);
  end;
 begin with G0 do 
  for i:=0 to cnt-2 do for j:=i+1 to cnt-1 do
  if Less(EA[i],EA[j]) then begin w:=EA[i]; EA[i]:=EA[j]; EA[j]:=w end;
 end;
 
procedure CreateHuffCodes(
 var HuffCodes: HuffCodesArr; var Huff_cnt:longint; c_mode:byte);
 var 
  Gen_cnt,i,j,n:longint;
  G0:TExoneSet; allowed:boolean;
 function CmpSet(var HS:TExoneSet):boolean;
  var succ:boolean; i:longint;
  begin
   succ:=HS.cnt=G0.cnt;
   if succ then for i:=0 to G0.cnt-1 
    do if HS.EA[i]<>G0.EA[i] then succ:=false;
   CmpSet:=succ; 
  end;
 procedure AddHSet;
  var i:longint; succ:boolean;
  begin
   succ:=true;
   for i:=0 to Huff_cnt-1 do 
    if CmpSet(HuffCodes[i]) then succ:=false;
   if succ and (Huff_cnt<ESet_max) then begin
    HuffCodes[Huff_cnt]:=G0;
    inc(Huff_cnt);
   end
  end;
 procedure PrintCodes;
  var i,j:longint;
  begin
   case c_mode of
    0:writeln(ttm,'------------- Huffman codes: --------------'); 
    1:writeln(ttm,'----------- Semi_Huffman codes: -----------'); 
   end;
   for i:=0 to Huff_cnt-1 do with HuffCodes[i] do begin
    write(ttm,'HuffSet[',i,'] cnt=',cnt,'   ');
    for j:=0 to cnt-1 do write(ttm,chr(ord('a')+j),'=',EA[j],' ');
    writeln(ttm);
   end;
   writeln(ttm,'-------------------------------------------'); 
   flush(ttm);
  end;

 procedure MakeNewSet(i,s_mode:byte);
  begin
   G0:=HuffCodes[Gen_cnt];
   with G0 do begin
    case s_mode of
     0:begin EA[cnt]:='-'+EA[i]; EA[i]:='+'+EA[i] end;
     1:EA[cnt]:='+'+EA[i]; 
     2:EA[cnt]:='-'+EA[i]; 
    end;
    inc(cnt);
   end;
   SortHSet(G0);
   AddHSet;
  end;

 function Test_Acc(i:byte):boolean;
  var j:byte; s0,s1:string;
  begin 
   Test_acc:=false;
   s0:=HuffCodes[Gen_cnt].EA[i];
   if s0[1]='-' then s0[1]:='+' else s0[1]:='-';
   with HuffCodes[Gen_cnt] do for j:=0 to n do begin
    s1:=EA[j];
    if length(s1)>length(s0) then delete(s1,1,length(s1)-length(s0)); 
    if s1=s0 then Test_acc:=true;
   end; 
  end;

 var mid_v:longint;
 begin
  InitHStat;
  
  with HuffCodes[0] do begin EA[0]:='+'; EA[1]:='-'; cnt:=2 end;
  HuffCodes[4]:=HuffCodes[0];                { 1-bit set } 
  with HuffCodes[0] do DoubleExones(EA,cnt); { 2-bit set }
  with HuffCodes[0] do DoubleExones(EA,cnt); { 3-bit set }
  HuffCodes[1]:=HuffCodes[0];
  with HuffCodes[1] do DoubleExones(EA,cnt); { 4-bit set }
  HuffCodes[2]:=HuffCodes[1];
  with HuffCodes[2] do DoubleExones(EA,cnt); { 5-bit set }
  HuffCodes[3]:=HuffCodes[2];
  with HuffCodes[3] do DoubleExones(EA,cnt); { 6-bit set }
  
  Huff_cnt:=5; Gen_cnt:=4;
  while (Huff_cnt>Gen_cnt) and (Huff_cnt<ESet_max) do begin
   n:=HuffCodes[Gen_cnt].cnt-1;
   if n<=Huff_size then for i:=0 to n do begin
    allowed:=true;
    with HuffCodes[Gen_cnt] do for j:=0 to n do 
     if (EA[j]='-'+EA[i]) or (EA[j]='+'+EA[i])
      then allowed:=false;
    if allowed then case c_mode of  
     0:MakeNewSet(i,0);
     1:begin
        if Test_acc(i) then MakeNewSet(i,0);
        MakeNewSet(i,1);
        MakeNewSet(i,2);
       end;
    end;
   end;
   inc(Gen_cnt);
  end;

  case c_mode of
   0:mid_v:=25;
   1:mid_v:=39;
  end;
  
  for i:=0 to 3 do begin { shift special codes }
   G0:=HuffCodes[0];
   for j:=1 to mid_v do HuffCodes[j-1]:=HuffCodes[j];
   HuffCodes[mid_v]:=G0; 
  end;
  
  PrintCodes;
 end;

const
 SqrEx_2:boolean=false;
 
procedure MakeEx_2(md,id:longint);
 var i:byte; G0:TExoneSet;
 begin 
  G0:=HuffCodes[id];
  if (G0.cnt<=7) and SqrEx_2 then begin
   SqrExones(G0.EA,G0.cnt);
   SortHSet(G0);
  end; 
  with G0 do case md of
   0:begin Lexones:=EA; Lex_cnt:=cnt end;
   1:begin Rexones:=EA; Rex_cnt:=cnt end;
  end;
  if md=0 then begin
   L_mask:=''; for i:=0 to Lex_cnt-1 do L_mask:=L_mask+'_';
  end else begin
   R_mask:=''; for i:=0 to Rex_cnt-1 do R_mask:=R_mask+'_';
  end;
 end;
 
procedure MakeEx_3(md,id:longint);
 var i:byte; G0:TExoneSet;
 begin 
  G0:=SemiCodes[id];
  with G0 do case md of
   0:begin Lexones:=EA; Lex_cnt:=cnt end;
   1:begin Rexones:=EA; Rex_cnt:=cnt end;
  end;
  if md=0 then begin
   L_mask:=''; for i:=0 to Lex_cnt-1 do L_mask:=L_mask+'_';
  end else begin
   R_mask:=''; for i:=0 to Rex_cnt-1 do R_mask:=R_mask+'_';
  end;
 end;


procedure Shoot(i,j,g_max:longint; mode,gram_mod,sh_mode:byte);
   function ProperEx(i:longint):boolean;
    var w:boolean;
    begin
     case sh_mode of
      0:w:=not (i in [{37}38..39]); 
      1:w:=not (i in [{23}24..25]);
     end;
     ProperEx:=w or (EL_base=128+64);
    end;
   var shs:string;
   begin if ProperEx(i) and ProperEx(j) then 
   if e_state in [0,mem_ov,too_lng] then begin
    case sh_mode of
     0:begin MakeEx_3(0,j); MakeEx_3(1,i); shs:='SGr_'; LR_mod:=0; end;
     1:begin MakeEx_2(0,j); MakeEx_2(1,i); shs:='HGr_'; LR_mod:=1; end;
    end; 
    Lex_id:=j; Rex_id:=i;
    case gram_mod of
     0:shs:='S'+shs;
     1:shs:='E'+shs;
     2:shs:='e'+shs;
    end; 

    TryExGFin(g_max,gram_mod);

    if e_state=exS2_l then begin
    
     GetHStat(4+sh_mode+2*gram_mod,H_eps,i,j,true);
      
     writeln(ttm,'M=',m,
       ' ',shs,mode,' H_eps=',H_eps,
       ' T_eps=',T_eps[0],'_',T_eps[1],
       ' i=',i,' j=',j,' g_cnt=',BBG_cnt); 
     flush(ttm);  

     case gram_mod of
      0:case mode of
         0:e_state:=ex0f_l;
         1,2:e_state:=ex1f_l;
        end; 
      1:case mode of
         0:e_state:=exH0_l;
         1,2:e_state:=exH1_l;
        end; 
      2:case mode of
         0:e_state:=exS0_l;
         1,2:e_state:=exS1_l;
        end; 
     end;

    end else begin
     { test_5388487 }
     { 
     if (i=39) and (j=39) then begin
      wr_grapf(ttm,BBG,BBG_cnt,false);
     end;
     }
    end; 
   end end;

procedure FastExones3(g_max:longint; mode,gram_mod:byte; all:boolean);
  procedure Loop(sh_mode:byte);
  var m_max:longint; 
   { 6 for up to 3 words in SemiHuffman code  } 
   { 35 for up to 4 words in SemiHuffman code  } 
   { 39 for up to 4 words in SemiHuffman code + spec sets } 
   { 173 for up to 5 words in SemiHuffman code + special sets } 
   { 795 for up to 6 words in SemiHuffman code + special sets } 
   { must be less than 1000 !!! }
  var i,j:longint;
  function i_max:longint;
   begin case sh_mode of
    0:case mode of
       0:i_max:=35 {13};
       1:i_max:=173;
       2:i_max:=795;
      end; 
    1:case mode of
       0:i_max:=21 {8};
       1:i_max:=67;
       2:i_max:=199;
      end;
   end end;
  function j_max:longint;
   begin case sh_mode of
    0:case mode of
       0:j_max:=6;
       1:j_max:=35;
       2:j_max:=173;
      end;
    1:case mode of
       0:j_max:=7 {2};
       1:j_max:=21;
       2:j_max:=67;
      end;
   end end;
  begin if e_state in [0,mem_ov,too_lng] then begin 
   HuffmanMode:=true;
   for i:=0 to i_max do if e_state in [0,mem_ov,too_lng]
   then if all or GetHStat0(4+sh_mode+2*gram_mod,H_eps,i) then begin
    gotoxy(55,7); write('SHG',sh_mode,'=',i,' eps=',H_eps,'  ');
    j:=i; 
    Shoot(i,i,g_max,mode,gram_mod,sh_mode);
    if i>j_max then m_max:=j_max else m_max:=i-1;
    if i>0 then for j:=0 to m_max do 
    if all or GetHStat(4+sh_mode+2*gram_mod,H_eps,i,j,false) then begin 
      Shoot(i,j,g_max,mode,gram_mod,sh_mode); 
      Shoot(j,i,g_max,mode,gram_mod,sh_mode) 
    end;
   end;
   HuffmanMode:=false;
  end end;
 begin
  Loop(0);
  Loop(1);
 end;

procedure TryBestEx(g_max:longint; l_mode:byte);
 var k:longint; gram_mod,sh_mode:byte;
 function i_max(sh_mode:byte):longint;
  begin case sh_mode of
   0:case l_mode of
      0:i_max:=35;
      1:i_max:=173;
      2:i_max:=Semi_cnt-1 {795};
     end; 
   1:case l_mode of
      0:i_max:=21;
      1:i_max:=199 {67};
      2:i_max:=Huff_cnt-1 {628} {199};
     end;
  end end;
 function ProperEx(j:word):boolean;
  begin
   ProperEx:=j<=i_max(sh_mode);
   if (sh_mode=0) and (l_mode<2) and (j in [38..39])
    then ProperEx:=false;
  end;
 begin
  HuffmanMode:=true;
  if H_St_cnt>0 then for k:=0 to H_St_cnt-1 do
   with H_Stats[k] do begin
    H_eps:=eps;
    sh_mode:=mode mod 2;
    gram_mod:=(mode-4) div 2;
    if ProperEx(j) and ProperEx(i) then begin
     gotoxy(55,7); write('mod=',mode,':',i,'|',j,'/',H_eps,' ',l_mode,'  ');
     Shoot(i,j,g_max,l_mode,gram_mod,sh_mode);
     if i<j then Shoot(j,i,g_max,l_mode,gram_mod,sh_mode);
    end;
   end; 
  HuffmanMode:=false;
 end;
 
procedure ShowESeq(i,j:word; sh_mode:byte);
 begin
  {
  H_eps:=0;
  T_eps[0]:=0;
  T_eps[1]:=0;
  HuffmanMode:=true;
  }
  case sh_mode of 
   0:begin MakeEx_3(0,i); MakeEx_3(1,j) end;
   1:begin MakeEx_2(0,i); MakeEx_2(1,j) end;
  end; 
  
  ClearExStats;
  MacroLoop(CEM,EMH,EMH_cnt,4,4*dump_max);
  wr_exones(ttm);
  flush(ttm);
 end;

procedure EvalBestEx(mode:byte; g_max:longint; all_ex:boolean);
 procedure Loop(sh_mode,vl_mode,vr_mode:byte);
  var l_max,r_max,i,steps:longint; l_r,r_r:real; best:boolean;
   { 6 for up to 3 words in SemiHuffman code  } 
   { 35 for up to 4 words in SemiHuffman code  } 
   { 39 for up to 4 words in SemiHuffman code + spec sets } 
   { 173 for up to 5 words in SemiHuffman code + special sets } 
   { 795 for up to 6 words in SemiHuffman code + special sets } 
   { must be less than 1000 !!! }
  function ProperEx(i:longint):boolean;
   begin
    case sh_mode of
     0:ProperEx:=all_ex or (not (i in [36..39])); 
     1:ProperEx:=not (i in [{23}22..25]);
    end; 
   end;
  procedure EvalSteps(i:longint);
   begin case sh_mode of
    0:begin
       steps:=500;
       case i of
        0..6:steps:=100;
        7..35:steps:=200;
        36:steps:=600;
        37:steps:=700;
        38:steps:=800;
        39:steps:=900;
        40..173:steps:=300;
       end; 
      end;
    1:begin
       steps:=600;
       case i of
        0..2:steps:=100;
        3..7:steps:=200;
        8..21:steps:=300;
        22:steps:=600;
        23:steps:=700;
        24:steps:=800;
        25:steps:=900;
        26..67:steps:=400;
       end; 
      end;
   end end;
  procedure Shoot1(i:longint);
   procedure EvalBest(
     Ex_cnt:word; var ExArr:TIntronArr; var ExStat:TExStat;
     var id_max:longint; var r:real; v_mode:byte);
    var r0:real; j,k:word;
    begin
     r0:=0.0; k:=0;
     for j:=0 to Ex_cnt-1 do if ExStat[j]>0 then inc(k);

     case v_mode of
      { OldBest: }
     0:begin
        if k=0 then begin
         writeln(ttm,'ERROR --> k=0 '); 
         wr_exones(ttm);
         flush(ttm);
         k:=10;
        end;
        for j:=0 to Ex_cnt-1 do if ExStat[j]>0 then begin
         r0:=r0+sqr(length(ExArr[j]){-1});
        end;
        r0:=sqrt(r0)/sqr(k); 
       end;
      { NewBest: } 
     1:if k=0 then r0:=0.0 else begin
        r0:=99.00; 
        for j:=0 to Ex_cnt-1 do if ExStat[j]>0 then
         if r0>length(ExArr[j]) then r0:=length(ExArr[j]);
        r0:=r0/sqrt(k); 
       end;
      { Best_2: }
     2,3:begin
        if k=0 then r0:=10.0 else begin
         r0:=0.0;
         for j:=0 to Ex_cnt-1 do if ExStat[j]>0 then case v_mode of
          2:r0:=r0+1.0/length(ExArr[j]);
          3:r0:=r0+1.0/sqr(length(ExArr[j]));
         end;
        end; 
        r0:=1.0/r0; 
       end;
     end;
     
     if r0>=r then begin id_max:=i; r:=r0; best:=true end;
    end;
   { 
   procedure Show;
    var k:word;
    begin
     writeln(ttm,'i= ',i,' sh_mode=',sh_mode,' steps=',steps);
     write(ttm,'LexStats: addr=',longint(addr(LexStat1)),'  ');
     for k:=0 to Lex_cnt-1 do write(ttm,LexStat1[k]:6);
     writeln(ttm);
     write(ttm,'RexStats: addr=',longint(addr(RexStat1)),'  ');
     for k:=0 to Rex_cnt-1 do write(ttm,RexStat1[k]:6);
     writeln(ttm);
     flush(ttm);
    end;
   } 
   var lim:longint;
   begin if ProperEx(i) then begin
    gotoxy(55,7); 
    case sh_mode of
     0:write('S_Best=',i:4,'   ');
     1:write('H_Best=',i:4,'   ');
    end; 
    case sh_mode of
     0:begin MakeEx_3(0,i); MakeEx_3(1,i) end;
     1:begin MakeEx_2(0,i); MakeEx_2(1,i) end;
    end; 
    ClearExStats;
    EvalSteps(i);
    lim:=steps*(mode+1)*3 div 2;
    if lim>cmax then lim:=cmax;
    { ExBug } {writeln(ttm,'B> i=',i,' e_state=',e_state); flush(ttm);}
    MacroLoop(CEM,EMH,EMH_cnt,4,lim);
    { ExBug } {writeln(ttm,'C> i=',i,' e_state=',e_state); flush(ttm);}
    { ExBug }
    {
    if e_state=1 then begin 
      wr_exones(ttm); flush(ttm);
    end;
    }
    e_state:=0;
    { Show; }
    EvalBest(Lex_cnt,Lexones,LexStat1,l_max,l_r,vl_mode);
    EvalBest(Rex_cnt,Rexones,RexStat1,r_max,r_r,vr_mode);
   end end;
  function i_max:longint;
   begin case sh_mode of
    0:case mode of
       0:i_max:=39 {35};
       1:i_max:=173;
       2:i_max:=Semi_cnt-1 {795};
      end; 
    1:case mode of
       0:i_max:=21;
       1:i_max:=199 {67};
       2:i_max:=Huff_cnt-1 {628} {199};
      end;
   end end;

  procedure TryProof;
   var he:byte;
   function lr_OK:boolean;
    begin
     case mode of
      0:lr_OK:=l_max+r_max>5;
      1:lr_OK:=l_max+r_max>50;
      2:lr_OK:=l_max+r_max>500;
     end; 
    end;
   begin
     for he:=0 to 4 {2} do if lr_OK then  begin
      H_eps:=he;
      Shoot(r_max,l_max,g_max,mode,2,sh_mode);
      Shoot(r_max,l_max,g_max,mode,0,sh_mode);
     end;  
   end;

  begin if e_state in [0,mem_ov,too_lng] then begin
   H_eps:=2 {1}; 
   l_r:=-1.0; r_r:=-1.0; 
   for i:=0 to i_max do 
   if e_state in [0,mem_ov,too_lng] then begin
    best:=false;
    Shoot1(i);
    if best then begin
     writeln(ttm,'Best: M=',m,' T_eps=',T_eps[0],'|',T_eps[1],
               ' l/r_id=',l_max,'|',r_max,
               ' l/r_v=',l_r:5:3,'|',r_r:5:3,
               ' SH:mode:vl|vr=',sh_mode,':',mode,':',vl_mode,'|',vr_mode);
     flush(ttm);    
     
     if l_max+r_max>1600 then ShowESeq(l_max,r_max,sh_mode); 
     
     TryProof;
     
     if not (e_state in [0,mem_ov,too_lng]) then writeln(ttm,
       'SuccBest for M=',m,
       ' SH:mode:vl|vr=',sh_mode,':',mode,':',vl_mode,'|',vr_mode);
    
    end;
   end; 
  end end;
 var vl,vr,hm:byte; 
 begin
  {T_eps[0]:=0; T_eps[1]:=0;}
  HuffmanMode:=true;
  for vl:=0 to 0{1..3} do 
   for vr:=0 to 0{1..3} do 
    for hm:=0 to 1 do Loop(hm,3-vl,3-vr);
  HuffmanMode:=false;
 end;

{ --------- Spectrum stats: -------- }
const
 SpecCnt:byte=0;
var
 SpecArr:array[byte] of string;
 SpecStr:string;

function  SpecCheck(s:string):boolean;
 var i:longint;
 begin
  SpecCheck:=false;
  if SpecCnt>0 then for i:=0 to SpecCnt-1 do
   if SpecArr[i]=s then SpecCheck:=true;
 end;
procedure SpecAdd(s:string);
 begin
  if (SpecCnt<255) and (not SpecCheck(s)) then begin
   inc(SpecCnt);
   SpecArr[SpecCnt]:=s;
  end;
 end;

procedure ExonesSpecFast(lim:longint);
 const 
  tsize=3 {3}; nreg0 = 0 {12};
 procedure Fast2(mode:byte; all:boolean);
  var i,j,g_max:longint;
  function Allow:boolean;
   begin
    Allow:=
     (mode>0) or ((T_eps[0]<=0) and (T_eps[1]<=0)) 
   end;
  function AllOK_0:boolean; 
   begin
    AllOK_0:=
        T_eps[0]+T_eps[1]<{=}0 
        {true} 
   end;
  begin
   for i:=0 to (tsize*tsize-1) do begin
    T_eps[0]:=(i mod tsize)-(tsize div 2);
    T_eps[1]:=(i div tsize)-(tsize div 2);
    gotoxy(55,4); 
    write('T_eps=',T_eps[0],',',T_eps[1],' ');
    if all then write('T') else write('F');

    case mode of
     0:if all
        then g_max:=gfin_max 
        else g_max:=gfin_max div 4;
     1:if all
        then g_max:=gfin_max*2
        else g_max:=gfin_max;
     2:g_max:=gfin_max*2;
    end; 

    if all then begin
     if AllOK_0 then EvalBestEx(mode,g_max,false);
      
     if mode>0 then for j:=0 to 3 do begin
      H_eps:=j;
      if AllOK_0 then FastExones3(g_max,mode-1,0,all);
      if AllOK_0 then FastExones3(g_max,mode-1,2,all); 
     end;
     
    end else begin
     if Allow then TryBestEx(g_max,mode);
    end;
    
   end; 
   gotoxy(55,4); write('                    ');
  end;
 begin if e_state in [0,mem_ov,too_lng] then begin
 
  if lim<600 then begin

   {EvalBestEx(2);}
   {ShowESeq(241,241);}
   {ShowESeq(241,30);}

   { 
   Fast2(2,false);
   Fast2(2,true);
   }
   
   Fast2(0,false);
  end else begin
   if lim<cmax
    then begin
     Fast2(1,false);
     if slow_0 then Fast2(0,true);  
    end else begin
     Fast2(2,false); 
    end; 
   if slow_scan and (lim=cmax) and 
      (not SpecCheck(SpecStr)) and
      (e_cnt[too_lng]>=nreg0)
    then begin
     Fast2(1,true);  
     if slow_2 then Fast2(2,true); 
    end; 
  end; 
  H_eps:=0;
  
 end end;
 
procedure TryBL_Pr_0(m_cnt:byte);
 { m_cnt must be >=1 }
 var
  DF:TDescr; simple,reps:boolean;
  k,i, Lex_0,Rex_0 :longint;
  stepmode:byte;
  steparr:array[0..cmax] of TDescr;
  stepcnt:longint;
 function OldVertex(var CTG:TGraph; CTG_cnt:longint):boolean;
  var j:longint; 
  begin
   OldVertex:=false;
   for j:=0 to CTG_cnt-1 do if SimMacro2(DF,CTG[j].D)
    then OldVertex:=true;
  end;
 procedure AddVertex(var CTG:TGraph; var CTG_cnt:longint);
  begin
   if not OldVertex(CTG,CTG_cnt) then if CTG_cnt<gfin_max then begin
    CTG[CTG_cnt].D:=DF;
    CTG[CTG_cnt].checked:=false;
    inc(CTG_cnt);
   end else pr_fail:=true;
  end;
 procedure Convert(
  var l,r:string;
  var Lexs:TIntronArr; var L_cnt:longint;
  var Rexs:TIntronArr; var R_cnt:longint);
  procedure PackL;
   var v1,v2:string; i0,e_cod:longint;
   begin
    if VarSCnt(l)>0 then begin
     v1:=GetVCnt(l);
     if { (v1='p') or } ((length(v1)>1) and (v1[2]='-')) 
      then pr_fail:=true
      else begin
       if v1[1]='p' then delete(v1,1,2);
       val(v1,i0,e_cod);
       if i0>m_cnt then i0:=m_cnt;
       Str(i0,v1);
       v1:='p+'+v1;
       SetVCnt(l,v1);
      end;
     if (not pr_fail) and (VarSCnt(l)>1) then begin
      i0:=Pos(')',l); v1:=copy(l,1,i0); delete(l,1,i0); 
      i0:=Pos('*',l);
      if i0=0 then i0:=Pos(')',l) else dec(i0); 
      v2:=copy(l,1,i0); delete(l,1,i0); 
      if l[1]<>'*' then l:='*'+l;
      AddIntron(Lexs,L_cnt,v2);
      l:=v1+l;
     end;
    end;
   end;
  procedure UnpackR;
   var j:integer; r0,r1,v1:string;
   begin 
    if r[1]='*' then begin
     simple:=false;
     stepmode:=1;
     stepcnt:=0;
     r1:=r; r0:=r; delete(r0,1,1);
     for j:=0 to R_cnt-1 do begin
      r:=Rexs[j]+r1; steparr[stepcnt]:=DF; inc(stepcnt);
      r:=Rexs[j]+r0; steparr[stepcnt]:=DF; inc(stepcnt);
     end;
     r:=r1;
    end else if VarSCnt(r)>0 then begin
     v1:=GetVCnt(r);
     if (length(v1)>1) and (v1[2]='-') then pr_fail:=true
    end;
   end;
  begin
   PackL;
   if not pr_fail then UnpackR;
  end;
 procedure MakeBL_Step;
  begin
   simple:=true;
   MakeMStep0(DF,3);
   if not pr_fail then if DF.md=1
    then Convert(DF.l,DF.r,Lexones,Lex_cnt,Rexones,Rex_cnt)
    else Convert(DF.r,DF.l,Rexones,Rex_cnt,Lexones,Lex_cnt);
  end;
 begin
  gotoxy(55, 8); write('BL_Proof M=',m,'  ');
 
  Lex_cnt:=0; Rex_cnt:=0;
  rep_min:=m_cnt-1;
  
  repeat
   Lex_0:=Lex_cnt;
   Rex_0:=Rex_cnt;
   
   ClearDescr(DF); 
   DF.af:=true; 
   pr_fail:=false;
   e_state:=0;
   BBG_cnt:=1; i:=0;
   with BBG[0] do begin D:=DF; checked:=false end;

   repeat
    DF:=BBG[i].D; BBG[i].checked:=true;

    BBGs_cnt:=1; BBGs[0].D:=DF;   
    repeat
     BBG[i].DNext:=DF;
     MakeBL_Step;
     if simple then begin
      reps:=OldVertex(BBGs,BBGs_cnt);
      if not reps then AddVertex(BBGs,BBGs_cnt);
     end else reps:=true; 
    until reps
          or OldVertex(BBG,BBG_cnt)
          or pr_fail;
          
    { if simple or (stepmode=0) then} BBG[i].DNext:=DF; 
    if not pr_fail then if simple 
     then AddVertex(BBG,BBG_cnt)
     else case stepmode of
      0:AddVertex(BBG,BBG_cnt);
      1,2,3:for k:=0 to stepcnt-1 do begin
        DF:=steparr[k];
        AddVertex(BBG,BBG_cnt);
       end; 
     end;

    inc(i)
   until (i=BBG_cnt) or pr_fail; 

  until pr_fail or ((Lex_0=Lex_cnt) and (Rex_0=Rex_cnt));

  if (not pr_fail) then begin
   e_state:=BLfinl;
   writeln(ttm,'M=',m,' BL_Proof  m_cnt=',m_cnt,'  g_cnt=',BBG_cnt);
  end; 
 end;

procedure TryBL_Proof;
 var k:byte;
 begin
  for k:=1 to 5 do { may be 4 is enough ! } 
   if e_state in [0,mem_ov,too_lng] 
    then TryBL_Pr_0(k);
 end;

const 
 best_rlen:byte=0;
 
procedure TryBL_Loop(lim:longint);
 var id_r:longint; succ:boolean;
 procedure FindMSRule(amd:byte);
  var i,j,cnt,cnt0:longint;
  begin
   cnt0:=-1; id_r:=-1;
   if SR_cnt>0 then for i:=0 to SR_cnt-1 do 
   with SRules[i] do if used and (md=amd) then begin
    cnt:=0; for j:=1 to spec_max do cnt:=cnt+j*spectrum[j]*length(c0);
    if cnt>cnt0 then begin cnt0:=cnt; id_r:=i; best_rlen:=length(c0) end;
   end;
  end;
 procedure FindOSRule;
  var i,k:longint; TR:TRule; w:char;
  begin 
   succ:=false;
   { old - hint ???
   with SSRules[0] do for i:=0 to ASR_cnt-1 
   do if md<>ASRules[i].md then 
   if (ASRules[i].c0=c1) and (not succ) then begin
    TR:=ASRules[i]; 
   } 
   with SSRules[0] do for i:=0 to SR_cnt-1 
   do if md<>SRules[i].md then 
   if (SRules[i].c0=c1) and (not succ) {and (SRules[i].used)} then begin
    TR:=SRules[i]; 
    for k:=0 to length(TR.c1)-1 do if not succ then begin
     if TR.c1=c0 then begin
      SSRules[1]:=TR;
      succ:=true;
     end else with TR do begin
      w:=c1[1]; delete(c1,1,1);
      c1:=c1+w; a:=a+w;
     end;
    end;
   end;
  end;
 procedure TryBLmd(amd:byte); 
  var i:longint;
  begin
   SSR_cnt:=2;
   FindMSRule(amd);
   SSRules[0]:=SRules[id_r];
   FindOSRule;

   { 
   wr_rules(ttm,'approved shift',SRules,SR_cnt,false);
   wr_rules(ttm,'Special ',SSRules,SSR_cnt,true); 
   flush(ttm); 
   } 
   
   if succ then begin
    for i:=0 to SSR_cnt-1 do SSRules[i].allowed:=true;
    rep_min:=0; rule_min:=0;
    MacroLoop(CEM,EMH,EMH_cnt,5,lim); 
    TryBL_Proof;
 
    { this is not solution: }
    { 
    for i:=0 to SSR_cnt-1 do with SSRules[i] do begin
     c0:=c0+c0; c1:=c1+c1; p:=p+p; c:=c+c;
    end;
    TryBL_Proof;
    }
    { 
    wr_rules(ttm,'approved shift',SRules,SR_cnt,false);
    wr_rules(ttm,'Special ',SSRules,SSR_cnt,true); 
    wr_macro_history(ttm,CEM,EMH,EMH_cnt,lim); 
    wr_ex1(ttm);
    wr_grapf(ttm,BBG,BBG_cnt,false); flush(ttm);
    flush(ttm); 
    }
   end; 
  end;
 begin
  TryBLmd(0);
  TryBLmd(1);
 end;
 
procedure loop_t({show:boolean;} s_x,s_y:byte);
 var 
  rm:array[byte] of word;
  rulem,rmin0,max_rid{,k_factor}:longint;

 procedure ShowRCnt(y:byte);
  var i:byte;
  begin
   gotoxy(1,y);
   for i:=1 to 25 do write(rm[i]:2,' ');
  end;

 function StrRCnt(y:byte):string;
  var i:byte; s,w:string;
  begin
   Str(ASR_cnt:4,w);
   s:=' |'+w+' |';
   for i:=1 to y do begin
    Str(rm[i]:3,w);
    s:=s+w;
   end;
   StrRCnt:=s;
  end;

 procedure EvalRCnt;
  var i:longint;
  begin
   for i:=1 to 255 do rm[i]:=0;
   if SR_cnt>0 then for i:=0 to SR_cnt-1 
    do inc(rm[length(SRules[i].c0)]);
  end;

 procedure clear1;
  var i:longint;
  begin
   EvalRCnt;
   rulem:=0; rule_min:=0;
   for i:=1 to 255 do if rm[i]>rulem then begin
    rulem:=rm[i]; 
    rule_min:=i;
   end;
   rmin0:=rule_min;
   rep_min:=1; 
  end;

 function RID_OK(i:byte):boolean;
  begin 
   RID_OK:=
    (i<>rmin0) and 
    ((rm[i]>(rulem div 3)) or (rm[i]>=2));
  end; 

 function AvRule:byte;
  var i,n:byte;
  begin
   n:=0;
   if max_rid>0 then for i:=1 to max_rid do 
    if RID_OK(i) then inc(n);
   AvRule:=n;  
  end;
  
 procedure clear1a;
  var OK:boolean;
  begin
   OK:=false;
   while not OK do begin
    if RID_OK(max_rid)
      then begin rule_min:=max_rid; OK:=true end;
    dec(max_rid);   
   end;
   if rule_min<dm then rep_min:=2
    else if rule_min<dm_2 then rep_min:=1
    else rep_min:=0; 
  end;
  
 procedure clear2(show:boolean);
  begin
{
  writeln(ttm,'M_20=',m,' e_state=',e_state,' rmin0=',rmin0); flush(ttm);
  writeln(ttm,'M_20=',m,' e_state=',e_state,' rmin0=',rmin0); flush(ttm);
}
   if (rmin0<=dm) and (rm[rmin0*2]=0) and show then begin
    rule_min:=rmin0;
    rep_min:=2;
   end else begin 
    rule_min:=0;
    if show
     then rep_min:=2
     else rep_min:=3; 
   end;
   if show then ShowRCnt(23);
  end;
  
 procedure clear0;
  begin
   rmin0:=0; rulem:=0;
   SR_cnt:=0; ASR_cnt:=0; BSR_cnt:=0;
   rep_min:=1; rule_min:=0;
   new_def:=true;
   e_state:=0;

   p_left:=0; p_right:=0;
   ClPosStat;
   ClearDescr(CD);
   SH_cnt:=0; 
  end; 
   
 procedure clear(enable:boolean);
  var i,j,n_max:longint;
  procedure EvalMaxUsed;
   var i,k,n:longint;
   begin
    n_max:=0;
    for i:=0 to SR_cnt-1 do begin
     n:=0;
     for k:=1 to spec_max do n:=n+SRules[i].spectrum[k]*k;
     if n>n_max then n_max:=n;
    end; 
   end;
  function BadRule(var SR:TRule):boolean;
   var n,k:longint;
   begin
    n:=0;
    { PackPatt tuning }
    for k:=1 to spec_max do n:=n+SR.spectrum[k]*k;
    BadRule:=n*3<n_max; 
   end;
  begin
   if enable then if SR_cnt>0 then for i:=0 to SR_cnt-1 do begin
    SRules[i].used:=false;
    SRules[i].allowed:=true;
    for j:=1 to spec_max do SRules[i].spectrum[j]:=0;
   end; 
   if not enable then begin
    EvalMaxUsed;
    for i:=0 to SR_cnt-1 do begin
     if BadRule(SRules[i]) 
      then SRules[i].allowed:=false;
     for j:=1 to spec_max do SRules[i].spectrum[j]:=0;
     SRules[i].used:=false;
    end;

    {
    writeln(ttm,'rule_min=',rule_min,'  rep_min=',rep_min);
    }
    if rule_min>0 then rep_min:=0;
    
   end; 
   
   IP_cnt:=0;
   ms_cnt:=0;
   fin_att:=0;

   ClearDescr(CM);
   MH_cnt:=0;
  end;

 procedure info1;
  begin
   {
   if show
    then begin
     gotoxy(1,24);writeln('info1 accesed in bad way !');
     Halt;
     wr_mash(s_x,s_y);
     gotoxy(s_x+1,s_y+7); write('c=',CM.c:6);
     gotoxy(s_x+1,s_y+8); write(MemUsed(CM),'/',sigma);
    end
    else begin
   } 
     inc(e_cnt[e_state]); 
     inc(m);
     if (m and 7)=0 then begin gotoxy(3,1); write(m:10) end; 
     if (m and 31)=0 then info0;
   { end }
  end; { info1 }

 procedure PassMacro(lim:longint);
  begin 
   {rep_min:=2;}
   clear(true);
   MacroLoop(CM,MH,MH_cnt,1,lim);

   { PackPatt tuning }
   if (e_state in [0,mem_ov,too_lng]) and
      (rule_min>0) and (lim>1000) 
    then begin

     { ttm_print }

     { 
     if rule_min in [6] then begin
      writeln(ttm,'-------------------');
      writeln(ttm);
      wr_mhistory(ttm,4000);
      writeln(ttm);
      CollatzLoop(Cl_M,ClMH,ClMH_cnt,cmax div 10);
       CM:=Cl_M;
       MH:=ClMH;
       MH_cnt:=ClMH_cnt;
      writeln(ttm,'-------------------');
      writeln(ttm);
      wr_mhistory(ttm,4000);
      writeln(ttm);
      flush(ttm);
      Halt;
     end;
     }
    
     clear(false);
     MacroLoop(CM,MH,MH_cnt,1,lim);
    end;

   {
   if e_state in [lNct_l,modf_l] then begin
    writeln(ttm,
     'M=',m,' Rule_min=',rule_min,
     ' k=',k_factor,' rep_min=',rep_min,
     ' e_state=',e_state);
   end;
   }
  end;

 procedure Pass1(frst:boolean; lim:longint);
  procedure Pass1a(rep:longint; k:longint);
  begin if e_state in [0,mem_ov,too_lng] then begin
   { k_factor:=k; }
   if frst then rule_min:=rep;
   {writeln(ttm,'rule_min=',rule_min,' lim=',lim); flush(ttm); }
   PassMacro(lim);
  end end;
  var k,k1,k2:longint;
  begin
   if frst then clear1 else clear1a;

   {
   if e_state in [0,mem_ov,too_lng] then 
    if rmin0>0 then Pass1a(rmin0,1);
   } 


   {
   if frst and (e_state in [0,mem_ov,too_lng]) and (lim=470) then begin
    rule_min:=6;
    PassMacro(cmax);
   end; 
   }

   for k1:=1 to dm+1 do if rm[k1]>0 then 
   for k2:=1 to dm+1 do if rm[k2]>0 then 
   if (k1*k2<=sr_lmax) and (rm[k1*k2]=0) and (lim>1000) and 
      frst and (e_state in [0,mem_ov,too_lng]) 
       then Pass1a(k1*k2,1);

       
   for k:=1 to dm+1 do if rm[k]>0 then begin
    if frst and (e_state in [0,mem_ov,too_lng]) 
       then Pass1a(k,1);

    {   
    if frst and (e_state in [mem_ov,too_lng]) and
       (rm[k*2]=0) then Pass1a(k*2,2);
    if frst and (e_state in [mem_ov,too_lng]) and
       (rm[k*3]=0) then Pass1a(k*3,3);
    if frst and (e_state in [mem_ov,too_lng]) and
       (rm[k*4]=0) then Pass1a(k*4,4);
    } 
    
   end;   
   
   if e_state in [0,mem_ov,too_lng] then 
    if rmin0>0 then Pass1a(rmin0,1);
    
  end;
  
 procedure Pass2(lim:longint);
  begin 
   {k_factor:=1;}
   clear2(lim=cmax);
   PassMacro(lim);
  end;
  
 procedure Pass0;
  begin
   clear0; 
{
  writeln(ttm,'M_c2=',m,' e_state=',e_state,' rmin0=',rmin0); flush(ttm);
}    
   repeat
    SH[SH_cnt]:=CD; inc(SH_cnt); 
    MakeMStep0(CD,0);
    if (e_state=0) then ShiftTest;
    if new_def and (e_state=0) then begin
     InvSTest;
     if (e_state=0) and lDum then back_track;
     new_def:=false;
    end;
    if e_state=0 then begin
     if ((SH_cnt>10) and (SH_cnt mod 200=70) and (SH_cnt<800)) 
        or (SH_cnt=1500) 
     then begin 
      SortRules;

      if e_state in [0,mem_ov,too_lng] then Pass2(SH_cnt); 
      if (e_state in [0,mem_ov,too_lng]) and (SH_cnt=1500) then begin
       { Pass2(SH_cnt); }
       TryBL_Loop(SH_cnt);
      end; 
      
      if e_state in [0,mem_ov,too_lng] then Pass1(true,SH_cnt); 

      if ((SH_cnt=470) or (SH_cnt=1500)) and
         (e_state in [0,mem_ov,too_lng]) 
       then ExonesSpecFast(SH_cnt); 

      if (e_state in [0,mem_ov,too_lng]) and (SH_cnt>200) then TryPFin_2; 
      if (e_state in [0,mem_ov,too_lng]) and (SH_cnt=470) then TryPFin_2_all(2); 
     end;   
     if e_state in [mem_ov,too_lng] then e_state:=0;  
    end else if e_state=nm_end then Pass2(cmax - 1 {SH_cnt+1});    
   until (e_state>0) or (SH_cnt>dm2qub);
   SortRules;
  end;

 procedure Pass100K(lim:longint);
  begin MacroLoop(CM,MH,MH_cnt,6,lim) end;
  
 function ShRecTest:boolean;
  begin
   ShRecTest:=(ASR_cnt<=20) and (dm>4);
   {
    (false or 
     ((dm>=5) and (not reversal) and (not SameDir)));
   }  
  end;

 const spec_max=15;
 var nrtyp:string;
 begin { loop_t }
  Pass0;
  if e_state in [0,mem_ov,too_lng] then begin

   if not ShRecTest then begin
    if e_state in [0,mem_ov,too_lng] then Pass100K(cmax div 5);
    if e_state in [0,mem_ov,too_lng] then TryPFin_2_all(dm);
    if e_state in [0,mem_ov,too_lng] then Pass1(true,cmax);
    max_rid:=sr_lmax*2;
    while (e_state in [0,mem_ov,too_lng]) and (AvRule>0)
     do Pass1(false,cmax);
    if e_state in [0,mem_ov,too_lng] then Pass2(cmax); 
    if e_state in [0,mem_ov,too_lng] then TryBL_Loop(SH_cnt);
    SpecStr:=StrRCnt(spec_max);
    if (e_state in [0,mem_ov,too_lng]) and (not slow_scan)
     then ExonesSpecFast(cmax);
    if e_state in [0,mem_ov,too_lng] then Pass100K(cmax);
    if e_state in [0,mem_ov,too_lng] then TryPFin_2_all(dm_2rR);
    if (e_state in [0,mem_ov,too_lng]) and (slow_scan)
     then ExonesSpecFast(cmax);
   end;

   if e_state in [0,mem_ov,too_lng] then begin {Pass2(cmax); }
    clear(true);
    rule_min:=best_rlen; rep_min:=1;
    MacroLoop(CM,MH,MH_cnt,1,cmax);
   end;
  end;
  
  info1;

  if e_state in [0,mem_ov,too_lng] then begin 
   if ShRecTest then begin
    writeln(tsrec,'M# = ',m-1); 
    wrf_m(tsrec,true,false,'ShRec');
    wr_rules(tsrec,'all shift',ASRules,ASR_cnt,true);
    wr_history(tsrec);
    flush(tsrec); 
    nrtyp:='SRec';
   end else nrtyp:='----';
   SpecStr:=StrRCnt(spec_max);
   SpecAdd(SpecStr);
   wrf_m(tnr1,e_cnt[mem_ov]+e_cnt[too_lng]<=1,false,nrtyp+SpecStr);
   flush(tnr1);
  end; 
  
 end; { loop_t }

procedure info_1(s_x,s_y:byte);
 begin
  wr_mash(s_x,s_y);
  gotoxy(s_x+1,s_y+7); write('c=',CM.c:6);
  gotoxy(s_x+1,s_y+8); write(MemUsed(CM),'/',sigma);
 end;
 
procedure wrf_m(var f:text; hd,sc:boolean; tstr:string);
 var i:byte; w:char;
 procedure wr(i:byte);
  begin
   if A[i]<>dum 
    then w:=chr(A[i]+ord('@'))
    else w:='x';
   if w='@' then w:='H';
   write(f,w);
   if C[i] in [0,1] 
    then write(f,C[i])
    else write(f,'x');
   if B[i] in [0,1] 
    then if B[i]=0 
     then write(f,'L ')
     else write(f,'R ')
    else write(f,'x ');
  end;
 begin
  if hd then begin
   for i:=1 to dm do begin
    w:=chr(i+ord('@'));
    write(f,w,'0  ',w,'1   ');
   end; 
   if sc
    then writeln(f,'   ones       steps')
    else writeln(f,'|    id    | type |SRcnt|          spectrum');
   writeln(f); 
  end; 
  for i:=1 to dm do begin
   wr(i); wr(i+dm); write(f,' ')
  end;
  if sc 
   then writeln(f,Sigma:7,CM.c:12) 
   else writeln(f,'|',m-1:9,' | ',tstr);
 end;

procedure wrf_tm(var f:text; var TM:machine);
 procedure wr_m0(X:t_arr; k:byte);
  var i:byte;
  begin
   for i:=k+1 to k+dm do if X[i]=dum
    then write(f,'x') else write(f,X[i]);
   for i:=dm to 8 do write(f,' ');
  end; 
 begin with TM do begin
  wr_m0(A,0); wr_m0(A,dm);
  wr_m0(B,0); wr_m0(B,dm);
  wr_m0(C,0); wr_m0(C,dm); 
  writeln(f);
 end end;

procedure EvalSigma(var CM:TDescr);
 function Cp(l:string):longint;
  var i,j:longint;
  begin
   j:=0;
   for i:=1 to length(l) do if l[i]='+' then inc(j);
   Cp:=j;
  end;
 procedure CountP(l:string);
  var n,i:longint; w1,w2:string;
  begin
   n:=Pos('(',l);
   if n>0 then begin
    if n>1 then begin
     sigma:=sigma+Cp(copy(l,1,n-1));
     delete(l,1,n-1);
    end;
    w1:=copy(l,2,Pos('|',l)-2);
    delete(l,1,Pos('|',l));
    w2:=copy(l,1,Pos(')',l)-1);
    delete(l,1,Pos(')',l));
    val(w2,n,i);
    sigma:=sigma+n*Cp(w1);
    CountP(l);
   end else sigma:=sigma+Cp(l);
  end;
 begin
  sigma:=0;  { why not 1 ? }
  CountP(CM.l);
  CountP(CM.r);
 end; 

var
 rec_min:longint;

procedure init_r;
 var dm0:byte;
 begin
  rec_min:=cmax;
  if SameDir then dm0:=dm-1 else dm0:=dm; 
  case dm0 of
   2:if reversal then rec_min:=1  else rec_min:=5;
   3:if reversal then rec_min:=10  else rec_min:=15;
   4:if reversal then rec_min:=40 else rec_min:=80;
   5:if reversal then rec_min:=800 else rec_min:=10000000;
   6:if reversal then rec_min:=10000000 else rec_min:=50000000;
  end;
  if Destructive then case dm of
   3,4:rec_min:=20;
   5:rec_min:=50;
   6:rec_min:=200;
  end;
 end;

procedure OnScreen(s_x,s_y:byte);
 begin
  wr_mash(s_x,s_y);
  gotoxy(s_x+1,s_y+7); write('c=',CM.c:6);
  gotoxy(s_x+1,s_y+8); write(MemUsed(CM),'/',sigma);
 end;
 
begin  { root }
 Str(dm,RevS);
 
 if Destructive then RevS:='DTM'+RevS else 
 case reversal of
  true: case SameDir of
         true: RevS:='STM'+RevS; 
         false:RevS:='RTM'+RevS; 
        end;
  false:case SameDir of
         true: RevS:='UTM'+RevS;
         false:RevS:='TM'+RevS;
        end; 
 end; 
 
 assign(tnr,   'noreg_' +RevS+'.txt'); rewrite(tnr); 
 assign(tnr1,  'nreg_'  +RevS+'.txt'); rewrite(tnr1); 
 assign(trc,   'recrd_' +RevS+'.txt'); rewrite(trc); 
 assign(tproof,'proved_'+RevS+'.txt'); rewrite(tproof); 
 assign(tsrec, 'ShRec_' +RevS+'.txt'); rewrite(tsrec); 
 assign(ttm,   'others.txt'); rewrite(ttm); 
 clrscr;  old_sec:=get_sec;
 rec_cnt:=0;
 CTG_cnt:=0;
 init_0;
 init_r;
 {init_ExSCnt;}
 CreateHuffCodes(HuffCodes,Huff_cnt,0);
 CreateHuffCodes(SemiCodes,Semi_cnt,1);
 
 for a1:=dm to dm+2 do { Full scan } 
 {a1:=dm+0;} {0,1,2}       { Partial scan }
 begin
  init_t(a1);
  repeat
   pull; 

   { 
   if m>=915350 then begin
    writeln(ttm,'M# = ',m); 
    wrf_m(ttm,true,false);
    flush(ttm);
   end; 
   }
   
   loop_t({false,}1,1);
   case e_state of
    nm_end,col0_e:begin
      if e_state=col0_e then begin
       CM:=Cl_M;
       MH:=ClMH;
       MH_cnt:=ClMH_cnt;
      end; 
      EvalSigma(CM);
      if CM.c>rec_min then begin
       wrf_m(trc,true,true,'');
       inc(rec_cnt);
       wr_rules(trc,'approved shift',SRules,SR_cnt,false);
       wr_mhistory(trc,cmax);
       flush(trc); 
      end;
      if CM.c>=t_record-dm+1 then begin
       if CM.c>=t_record then t_record:=CM.c; 
       if e_state=nm_end 
        then info_1(sh_ct1,1) {loop_t(true,sh_ct1,1)} 
        else OnScreen(sh_ct1,1);
       inc(sh_ct1,12); if sh_ct1=50 then sh_ct1:=14;
      end;

      if (e_state=col0_e) and (e_cnt[e_state]<=showmax) then begin
       writeln(tproof,'M# = ',m-1); 
       wrf_m(tproof,true,true,'');
       writeln(tproof,'------- Collatz-like machine: ------');
       wr_rules(tproof,'approved shift',SRules,SR_cnt,false);
       wr_mhistory(tproof,cmax);
       wr_grapf(tproof,CTG,CTG_cnt,false);
       writeln(tproof,'-------------------------------------');
      end;
       
      if sigma>s_record then begin
       s_record:=sigma; 
       if e_state=nm_end
        then info_1(sh_ct2,12) {loop_t(true,sh_ct2,12)}
        else OnScreen(sh_ct2,12);
       inc(sh_ct2,12); if sh_ct2=50 then sh_ct2:=14;
      end;
     end; 
    mem_ov,too_lng:
     if e_cnt[e_state]<=2*showmax then begin
      writeln(tnr,'M# = ',m-1); 
      wrf_m(tnr,true,false,'nonregular');
      wr_brules(tnr,'basic shift', BSRules,BSR_cnt,true);
      writeln(tnr,'Main Rule ID = ',BBR_id);
      {
      wr_bhistory(tnr,dump_max);
      if BBR_id>=0 then begin
       wr_grapf(tnr,BBG,BBG_cnt,false);
       wr_mmhistory(tnr,dump_max*2);
      end;
      }
      { 
      wr_rules(tnr,'all shift',     ASRules,ASR_cnt,true);
      wr_rules(tnr,'approved shift',SRules,SR_cnt,true);
      }
      wr_rules(tnr,'approved shift',SRules,SR_cnt,false);
      wr_mhistory(tnr,cmax);
      wr_history(tnr);
      WrPosStat(tnr);
      {
      wr_pproof_3(tnr);
      wr_grapf(tnr,CTG,CTG_cnt,false);
      }
      writeln(tnr,
       '====================================================');
      flush(tnr); 
     end;
    lNct_l,BLfinl,modf_l,
    pfin_l,swpf_l,ex0f_l,ex1f_l,
    exS0_l..exS2_l,
    exH0_l..exH1_l:
     if e_cnt[e_state]<=showmax then begin
      writeln(tproof,'M# = ',m-1); 
      wrf_m(tproof,true,false,'infinite');
      case e_state of
       lNct_l,modf_l:begin
         wr_rules(tproof,'approved shift',SRules,SR_cnt,false);
         wr_mhistory(tproof,dump_max);
         case e_state of
          lNct_l:begin
            writeln(tproof,'Incremental Formula test passed !');
           end;
          modf_l:begin
            writeln(tproof,'Closed Transition Modulo_Graph test passed !');
           end;
         end;  
         wr_grapf(tproof,CTG,CTG_cnt,false);
        end;
       BLfinl:begin 
          wr_rules(tproof,'Special ',SSRules,SSR_cnt,true); 
          wr_macro_history(tproof,CEM,EMH,EMH_cnt,dump_max); 
          writeln(tproof,'BL_Proof succeed !');
          wr_ex1(tproof);
          wr_grapf(tproof,BBG,BBG_cnt,false); 
        end; 
       pfin_l:begin
         wr_history(tproof);
         WrPosStat(tproof);
         wr_pproof_3(tproof);
         writeln(tproof,'Closed Position test passed !');
        end;
       swpf_l:begin
         wr_brules(tproof,'basic shift', BSRules,BSR_cnt,true);
         writeln(tproof,'Main Rule ID = ',BBR_id);
         wr_bmhistory(tproof,dump_max);
         writeln(tproof,'BinVortex (Lemma1 + linear) test passed !');
        end;
       ex0f_l,ex1f_l,exS0_l..exS2_l,exH0_l..exH1_l:begin
         { wr_bhistory(tproof,dump_max); }
         case e_state of
          ex0f_l:writeln(tproof,'Single exone test proof:');
          ex1f_l:writeln(tproof,'Self_tuning exone test proof:');
          exS0_l:writeln(tproof,'Spec0 exone test proof:');
          exS1_l:writeln(tproof,'Spec1 exone test proof:');
          exS2_l:writeln(tproof,'Spec2 exone test proof:');
          exH0_l:writeln(tproof,'SpecH0 exone test proof:');
          exH1_l:writeln(tproof,'SpecH1 exone test proof:');
         end;
         {
         wr_brules(tproof,'basic shift',BSRules,BSR_cnt,true);
         writeln(tproof,'Basic Rule ID = ',BBR_id);
         }
         wr_exones(tproof);
         {
         if e_state in [exS0_l..exS2_l] then wr_extuples(tproof);
         wr_grapf(tproof,BBG,BBG_cnt,e_state in [exS0_l..exS2_l]);
         }
         wr_grapf(tproof,BBG,BBG_cnt,false);
         writeln(tproof,'finite exones graph test passed !');
        end;
      end;
      writeln(tproof,
       '====================================================');
      flush(tproof); 
     end;
   end;
  until s_ct=0;
  gotoxy(1,24);
  write(a1,' loop finished ! '); 
 end;
 info0;
 writeln;
 close(tsrec);
 close(tnr); 
 close(tnr1); 
 close(trc); 
 close(ttm); 
 close(tproof);
 gotoxy(1,24);
end. { root }
