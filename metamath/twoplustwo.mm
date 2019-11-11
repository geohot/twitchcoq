$[ lib/peano.mm $]

wff_pa_ax1 $p wff not = 0 S x $=
  tzero varx tvar tsucc binpred_equals wff_atom wff_not
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
cheat2 $p |- forall x implies = x 0 not = 0 S x $=
varx quant_all varx wff_pa_ax1 wff_quant
varx quant_all logbinopimplies varx wff_pa_ax1 varx tvar tzero binpred_equals wff_atom wff_logbinop wff_quant
varx nocheat
tzero varx varx wff_pa_ax1 all_elim
ax-mp
$.

$( two_plus_two_eq_four $a |- = + S S 0 S S 0 S S S S 0 $. $)

$(
varx vary pa_ax4

varx tvar

if forall x, f(x) and x=t then f(t)

$)


$( all_elim: forall x, phi -> forall x, (x = t) -> phi $)

$(

(forall x, phi) t- > (forall x, x=t -> phi)

tzero varx varx wff_pa_ax1 all_elim

|- not = 0 S x
|- forall x, not = 0 S x

phi = varx pa_ax1_wff
psi = wff_psi
ax-1

varx wff_pa_ax1 logbinopimplies varx wff_pa_ax1 wff_psi wff_logbinop varx wff_pa_ax1 logbinopimplies tbinop varx pa_ax1 varx wff_pa_ax1 wff_psi ax-1 ax-mp

phi = wff_psi

varx wff_psi varx wff_pa_ax1 varx wff_psi int1 alpha_2

phi = not = 0 S x
psi = implies chi not = 0 S x
min = varx pa_ax1
maj = varx wff_pa_ax1 wff-chi ax-1

varx wff_pa_ax1
logbinopimplies varx wff_pa_ax1 wff-chi wff_logbinop
varx pa_ax1
varx wff_pa_ax1 wff-chi ax-1
ax-mp

varx wff_pa_ax1 logbinopimplies varx wff_pa_ax1 wff-chi wff_logbinop varx pa_ax1 varx wff_pa_ax1 wff-chi ax-1 ax-mp



varx wff_pa_ax1 wff-chi ax-1



implies phi chi

varx pa_ax1

alpha_hyp2


phi = phi
x = varx
chi = not = 0 S x

alpha_2

wff_phi tzero varx tvar tsucc binpred_equals wff_atom wff_not varx alpha_2


phi = |- not = 0 S x
psi = |- not = 0 S 0


|- not = 0 S x -> |- not = 0 S 0

test $p |- not = 0 S y $=
$.

$)

$(

x: x
t: 0
phi: not = 0 S x
chi: not = 0 S 0
all_elim3

forall x, x=t -> x!=(S x) 0!=(S x)


tzero varx tzero varx tvar tsucc binpred_equals wff_atom wff_not all_elim


|- implies
   forall x, 0 != S x -> forall x, x=0 -> 0 != S x


tzero varx tvar tsucc binpred_equals wff_atom wff_not
tzero tzero tsucc binpred_equals wff_atom wff_not

tzero tzero tsucc binpred_equals wff_atom wff_not
tzero pa_ax1 $.

tzero tsucc tsucc tzero tsucc tsucc binop_plus tbinop
tzero tsucc tsucc tsucc tsucc
binpred_equals wff_atom
$.
$)

