$c M I U |- wff $.
$v x y $.

wx $f wff x $.
wy $f wff y $.

we $a wff $.
wM $a wff x M $.
wI $a wff x I $.
wU $a wff x U $.

ax $a |- M I $.

${
  Ia $e |- x I $.
  I_ $a |- x I U $.
$}

${
  IIa $e |- M x $.
  II  $a |- M x x $.
$}

${
  IIIa $e |- x I I I y $.
  III  $a |- x U y $.
$}

${
  IVa $e |- x U U y $.
  IV  $a |- x y $.
$}

trivial $p |- M I $=
  ax
$.

lesstrivial $p |- M I I $=
  we wI ax II
$.

theorem1 $p |- M U I I U $=
  we wM wU wI we wI wU
    we wU wI wU
      we wM we wI wU
        we wM wI wI wI
          we wI wI
            we wI ax II
          II
        I_
      III
    II
  IV
$.

