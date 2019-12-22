$[ lib/peano.mm $]

$(
  Doing this sort of thing from the bottom on stream is an impressive undertaking.
  Unfortunately, there are a bunch of prerequisites needed to really get anywhere
  starting from just the axioms, and propositional logic is a big one. In order to
  have a good time using propositional logic, you need a library of ~200 basic
  theorems in propositional logic. I will not do this, but instead just prove a few
  requirements for the theorems of interest today.

  These proofs are primarily borrowed from peano.mm1, which were themselves borrowed
  from set.mm proofs. -Mario
$)

${
  mpd.1 $e |- implies phi psi $.
  mpd.2 $e |- implies phi implies psi chi $.
  $( A -> B, A -> B -> C |- A -> C $)
  mpd $p |- implies phi chi $=
    ( logbinopimplies wff_logbinop ax-2 ax-mp ) FBAGZFCAGZDFFCBGAGFKJGEABCHII
    $.
$}

${
  syl.1 $e |- implies phi psi $.
  syl.2 $e |- implies psi chi $.
  $( A -> B, B -> C |- A -> C $)
  syl $p |- implies phi chi $=
    ( logbinopimplies wff_logbinop ax-1 ax-mp mpd ) ABCDFCBGZFKAGEKAHIJ $.
$}

$( A -> A $)
id $p |- implies phi phi $=
  ( logbinopimplies wff_logbinop ax-1 mpd ) ABAACZAAADAFDE $.

$( !A -> A -> B $)
absurd $p |- implies not phi implies phi psi $=
  ( wff_not logbinopimplies wff_logbinop ax-1 ax-3 syl ) ACZDIBCZEDBAEIJFBAGH
  $.

${
  com12.1 $e |- implies phi implies psi chi $.
  $( A -> B -> C |- B -> A -> C $)
  com12 $p |- implies psi implies phi chi $=
    ( logbinopimplies wff_logbinop ax-1 ax-2 ax-mp syl ) BEBAFZECAFZBAGEECBFAFE
    LKFDABCHIJ $.
$}

${
  imidm.1 $e |- implies phi implies phi psi $.
  $( A -> A -> B |- A -> B $)
  imidm $p |- implies phi psi $=
    ( logbinopimplies wff_logbinop id com12 mpd ) ADBAEZBCIABIFGH $.
$}

$( (!A -> A) -> A $)
contra $p |- implies implies not phi phi phi $=
  ( logbinopimplies wff_not wff_logbinop absurd ax-2 ax-mp ax-3 syl imidm ) BA
  ACZDZALBLCZKDZBALDBBMADKDBNLDAMEKAMFGALHIJ $.

$( !!A -> A $)
notnot2 $p |- implies not not phi phi $=
  ( wff_not logbinopimplies wff_logbinop absurd contra syl ) ABZBCAHDAHAEAFG
  $.

$( (B -> C) -> (A -> B) -> (A -> C) $)
imim2 $p |- implies implies psi chi
            implies implies phi psi
                    implies phi chi $=
  ( logbinopimplies wff_logbinop ax-1 ax-2 syl ) DCBEZDIAEDDCAEDBAEEIAFABCGH
  $.

$( (A -> !B) -> (B -> !A) $)
con2 $p |- implies implies phi not psi
                   implies psi not phi $=
  ( logbinopimplies wff_not wff_logbinop notnot2 imim2 com12 ax-mp ax-3 syl )
  CBDZAEZCLADZDZEZCNBECAOEZCPMEAFMQPOALGHINBJK $.

$( A -> !!A $)
notnot1 $p |- implies phi not not phi $=
  ( logbinopimplies wff_not wff_logbinop id con2 ax-mp ) BACZHDBHCADHEHAFG $.

${
  con1i.1 $e |- implies not phi psi $.
  $( !A -> B |- !B -> A $)
  con1i $p |- implies not psi phi $=
    ( logbinopimplies wff_not wff_logbinop notnot1 syl ax-3 ax-mp ) DBEZEZAEZFD
    AKFMBLCBGHAKIJ $.
$}

$( (A -> B) -> (!B -> !A) $)
con3 $p |- implies implies phi psi
                   implies not psi not phi $=
  ( logbinopimplies wff_logbinop wff_not notnot1 imim2 ax-mp con2 syl ) CBADZC
  BEZEZADZCAELDCMBDCNKDBFABMGHALIJ $.

$( A /\ B -> A $)
andL $p |- implies and phi psi phi $=
  ( logbinopand wff_logbinop logbinopimplies logbinopiff df-an bi1 ax-mp
  absurd wff_not con1i syl ) CBADZEBKZADZKZAFQNDEQNDABGNQHIAPAOJLM $.

$( A /\ B -> B $)
andR $p |- implies and phi psi psi $=
  ( logbinopand wff_logbinop logbinopimplies wff_not logbinopiff df-an bi1
  ax-1 ax-mp con1i syl ) CBADZEBFZADZFZBGQNDEQNDABHNQIKBPOAJLM $.

$( A -> B -> A /\ B $)
andI $p |- implies phi implies psi and phi psi $=
  ( logbinopimplies wff_not wff_logbinop logbinopand com12 con2 syl
  logbinopiff id df-an bi2 ax-mp imim2 ) ACCBDZAEZDZBEZCFBAEZBEZACPQESQAPQKGQBH
  ICTREZCUASEJRTEUBABLTRMNBRTONI $.

${
  andId.1 $e |- implies phi psi $.
  andId.2 $e |- implies phi chi $.
  $( A -> B -> A /\ B $)
  andId $p |- implies phi and psi chi $=
    ( logbinopand wff_logbinop logbinopimplies andI syl mpd ) ACFCBGZEABHLCGDBC
    IJK $.
$}

${
  imp.1 $e |- implies phi implies psi chi $.
  $( A -> B -> C |- A /\ B -> C $)
  imp $p |- implies and phi psi chi $=
    ( logbinopand wff_logbinop andR logbinopimplies andL syl mpd ) EBAFZBCABGLA
    HCBFABIDJK $.
$}

${
  exp.1 $e |- implies and phi psi chi $.
  $( A /\ B -> C |- A -> B -> C $)
  exp $p |- implies phi implies psi chi $=
    ( logbinopimplies logbinopand wff_logbinop andI imim2 ax-mp syl ) AEFBAGZBG
    ZECBGZABHECLGENMGDBLCIJK $.
$}

wff_pa_ax1 $p wff not = 0 S x $=
  tzero varx tvar tsucc binpred_equals wff_atom wff_not
$.

wff_pa_ax1_term $p wff not = 0 S t $=
  tzero tt tsucc binpred_equals wff_atom wff_not
$.

$(
  phi $b varx wff_pa_ax1
  psi $b logbinopimplies varx wff_pa_ax1 wff-chi wff_logbinop
  ax-mp
$)

int1 $p |- implies chi not = 0 S x $=
  varx wff_pa_ax1
  logbinopimplies varx wff_pa_ax1 wff-chi wff_logbinop
    varx pa_ax1
    varx wff_pa_ax1 wff-chi ax-1
  ax-mp
$.

${
  $d psi x $.
  $d x y $.

  int2 $p |- implies psi forall x not = 0 S x $=
    varx wff_psi varx wff_pa_ax1 varx wff_psi int1 alpha_2
  $.

  $(
    phi: vary wff_pa_ax1
    psi: varx quant_all varx wff_pa_ax1 wff_quant
    min: vary pa_ax1
    maj: varx vary wff_pa_ax1 int2
    ax-mp
  $)

  nocheat $p |- forall x not = 0 S x $=
    vary wff_pa_ax1
    varx quant_all varx wff_pa_ax1 wff_quant
    vary pa_ax1
    varx vary wff_pa_ax1 int2
    ax-mp
  $.
$}

$(
phi: varx quant_all varx wff_pa_ax1 wff_quant
   = wff forall x not = 0 S x
psi: varx quant_all logbinopimplies varx wff_pa_ax1 varx tvar tzero binpred_equals wff_atom wff_logbinop wff_quant
   = wff forall x implies = x 0 not = 0 S x
min: varx cheat
   = |- forall x not = 0 S x
maj: tzero varx varx wff_pa_ax1 all_elim
   = |- implies forall x not = 0 S x forall x implies = x 0 not = 0 S x
ax-mp
$)

$( forall x, x=0 -> 0 != S x $)
nocheat2 $p |- forall x implies = x 0 not = 0 S x $=
varx quant_all varx wff_pa_ax1 wff_quant
varx quant_all logbinopimplies varx wff_pa_ax1 varx tvar tzero binpred_equals wff_atom wff_logbinop wff_quant
varx nocheat
tzero varx varx wff_pa_ax1 all_elim
ax-mp
$.

nocheat2_wff $p wff forall x implies = x 0 not = 0 S x $=
  varx quant_all logbinopimplies varx tvar wff_pa_ax1_term varx tvar tzero binpred_equals wff_atom wff_logbinop wff_quant
$.

$( (forall x, forall y, x=y -> phi<->psi) -> forall x, phi <-> forall y, psi $)

tmp3 $p |- implies and = t t = x 0 iff = t x = t 0 $=
tt tt varx tvar tzero binpred_equals eq-congr
$.

tmp3a $p |- implies = x 0 = S x S 0 $=
  varx tvar tzero eq-suc
$.

$( x = 0 -> (0 != S x <-> 0 != S 0) $)
$(
  s0 = S x
  s1 = S 0
  t0 = 0
  t1 = 0
  binpred_equals
  eq-congr -> iff = 0 S x = 0 S 0
$)

tmp3b $p |- implies and = 0 0 = S x S 0 iff = 0 S x = 0 S 0 $=
  tzero
  tzero
  varx tvar tsucc
  tzero tsucc
  binpred_equals
  eq-congr
$.

tmp3c $p |- implies = S x S 0 and = 0 0 = S x S 0 $=
  ( tzero binpred_equals wff_atom logbinopimplies logbinopand tvar
  wff_logbinop tsucc eq-refl andI ax-mp ) BBCDZEFAGIBICDZMHNHBJMNKL $.

eqeq2 $p |- implies = s t iff = u s = u t $=
  ( binpred_equals wff_atom logbinopimplies logbinopiff logbinopand andR
  eq-sym wff_logbinop andL syl andId eq-trans exp bi3 mpd ) ABDEZFCADEZCBDEZKZG
  UATKZSUATHUASKZHBADEZUAKTUDUAUESUAIUDSUESUALABJMNCBAOMPSFUATKFUCUBKSTUAHTSKZH
  STKUAUFTSSTISTLNCABOMPTUAQMR $.

$(
  phi: = S x S 0
  psi: and = 0 0 = S x S 0
  chi: iff = 0 S x = 0 S 0
$)

tmp3d $p |- implies = S x S 0 iff = 0 S x = 0 S 0 $=
  ( tvar tsucc tzero eqeq2 ) ABCDCDE $.

$(
  phi: = x 0
  psi: = S x S 0
  chi: iff = 0 S x = 0 S 0
$)

tmp3e $p |- implies = x 0 iff = 0 S x = 0 S 0 $=
  ( tvar tzero binpred_equals wff_atom tsucc logbinopiff wff_logbinop tmp3d
  syl eq-suc ) ABZCDELFZCFZDEGCNDECMDEHLCKAIJ $.

$( using ax-3 $)

$( (A <-> B) -> (!A <-> !B) $)
notbi $p |- implies iff phi psi iff not phi not psi $=
  ( logbinopiff wff_logbinop logbinopimplies wff_not bi1 con3 syl bi2 bi3 mpd
  ) CBADZEAFZBFZDZCONDZMEBADPABGABHIMEONDZEQPDMEABDRABJBAHINOKIL $.

tmp3f $p |- implies iff = 0 S x = 0 S 0 iff not = 0 S x not = 0 S 0 $=
  ( tzero tvar tsucc binpred_equals wff_atom notbi ) BACDEFBBDEFG $.

$(
  phi: = x 0
  psi: iff = 0 S x = 0 S 0
  chi: iff not = 0 S x not = 0 S 0
  phi -> psi = tmp3e
  psi -> chi = tmp3f
$)

cheat3 $p |- implies = x 0 iff not = 0 S x not = 0 S 0 $=
  ( tvar tzero binpred_equals wff_atom logbinopiff tsucc wff_logbinop tmp3e
  syl wff_not tmp3f ) ABZCDEFCCGDEZCMGDEZHFNKOKHAIALJ $.

$( t,x,phi,chi,all_elim3_hyp1 $)
nocheat4 $p |- implies
    forall x implies = x 0 not = 0 S x
  not = 0 S 0 $=
tzero
varx
varx tvar wff_pa_ax1_term
tzero wff_pa_ax1_term
varx cheat3
all_elim3
$.

one_ne_zero $p |- not = 0 S 0 $=
varx nocheat2_wff
tzero wff_pa_ax1_term
varx nocheat2
varx nocheat4
ax-mp
$.

