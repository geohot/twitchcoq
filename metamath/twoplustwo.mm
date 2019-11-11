$[ lib/peano.mm $]

wff_pa_ax1 $p wff not = 0 S x $=
  tzero varx tvar tsucc binpred_equals wff_atom wff_not
$.

wff_pa_ax1_term $p wff not = 0 S t $=
  tzero tt tsucc binpred_equals wff_atom wff_not
$.

int1 $p |- implies chi not = 0 S x $=
  varx wff_pa_ax1 logbinopimplies varx wff_pa_ax1 wff-chi wff_logbinop varx pa_ax1 varx wff_pa_ax1 wff-chi ax-1 ax-mp
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

tmp3c $a |- implies = S x S 0 and = 0 0 = S x S 0 $.

$(
  phi: = S x S 0
  psi: and = 0 0 = S x S 0
  chi: iff = 0 S x = 0 S 0
$)

tmp3d $a |- implies = S x S 0 iff = 0 S x = 0 S 0 $.

$(
  phi: = x 0
  psi: = S x S 0
  chi: iff = 0 S x = 0 S 0
$)

tmp3e $a |- implies = x 0 iff = 0 S x = 0 S 0 $.

$( using ax-3 $)

tmp3f $a |- implies iff 0 S x = 0 S 0 iff not = 0 S x not = 0 S 0 $.

$(
  phi: = x 0
  psi: iff = 0 S x = 0 S 0
  chi: iff not = 0 S x not = 0 S 0
  phi -> psi = tmp3e
  psi -> chi = tmp3f
$)

cheat3 $a |- implies = x 0 iff not = 0 S x not = 0 S 0 $.

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

