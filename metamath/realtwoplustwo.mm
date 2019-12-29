$[ twoplustwo.mm $]

$(
  We're going to replicate most of the work done for one_ne_zero
  for the other axioms, so that we can have terms instead of vars.
$)

${
  $( phi |- A. x phi $)
  gen.1 $e |- phi $.
  $( This is an axiom in set.mm, but here it has a (somewhat convoluted) proof. $)
  gen $p |- forall x phi $=
    ( quant_all tzero binpred_equals wff_quant eq-refl eq-sym ax-mp logbinopiff
    wff_atom alpha_2 wff_logbinop logbinopimplies ax-1 bi3 alpha_1 bi1 ) ADEEFL
    ZGZADBGZTUAEHZATTEEIMJKUBUANZOUBUANTUDUCADTTBKBTNZOUETNOTBNZUETUFUCTBPJOBTN
    ZOUEUFNBUGCBTPJTBQJJUETPJRJUAUBSJJ $.
$}

${
  $d x psi $.  $d x t $.
  $( x = t -> (A <-> B), A |- B $)
  var_to_term.1 $e |- implies = x t iff phi psi $.
  var_to_term.2 $e |- phi $.
  $(
    This is the main theorem needed for the var/term transformations.
    In set.mm it's called vtocl for "var to class", but here it's more
    like var to term.
  $)
  var_to_term $p |- psi $=
    ( quant_all logbinopimplies tvar binpred_equals wff_atom wff_quant all_elim
    wff_logbinop gen ax-mp all_elim3 ) BGHCBIAJKNLZDBGCLRBCFOABCMPABCDEQP $.
$}

$( Oops, ran out of variables. let's make some new wffs. $)
$v psi2 chi2 $.
wpsi2 $f wff psi2 $.
wchi2 $f wff chi2 $.

biid $p |- iff phi phi $=
  ( logbinopimplies wff_logbinop logbinopiff id bi3 ax-mp ) BAACZDAACZAEZHBIHC
  JAAFGG $.

biidd $p |- implies phi iff psi psi $=
  ( logbinopiff wff_logbinop logbinopimplies biid ax-1 ax-mp ) CBBDZEIADBFIAGH
  $.

eqidd $p |- implies phi = t t $=
  ( binpred_equals wff_atom logbinopimplies wff_logbinop eq-refl ax-1 ax-mp )
  AACDZEJBFAGJBHI $.

eqeq1 $p |- implies = s t iff = s u = t u $=
  ( wff_atom logbinopimplies wff_logbinop logbinopiff eq-trans logbinopand
  andL binpred_equals exp eq-sym syl andR andId bi3 mpd ) ABKDZEACKDZBCKDZFZGUA
  TFZSUATABCHLSEUATFEUCUBFSTUAITSFZITBAKDZFUAUDUETUDSUESTJABMNSTOPBACHNLTUAQNR
  $.

${
  $( A -> (B1 <-> B2), A -> (C1 <-> C2) |- A -> ((B1 -> C1) <-> (B2 -> C2)) $)
  imbid.1 $e |- implies phi iff psi psi2 $.
  imbid.2 $e |- implies phi iff chi chi2 $.
  imbid $p |- implies phi iff implies psi chi implies psi2 chi2 $=
    ( logbinopimplies wff_logbinop logbinopiff bi1 syl imim2 com12 bi2 mpd bi3
    ) AHHCBIZHEDIZIZJSRIZAHHEBIZSIZTAHDBIZUCAJDBIZUDFBDKLSUDUBBDEMNLAHRUBIZHTUC
    IAHCEIZUFAJECIZUGGCEOLBECMLSUBRMLPAHSRIZHUATIAHHCDIZRIZUIAHBDIZUKAUEULFBDOL
    RULUJDBCMNLAHSUJIZHUIUKIAHECIZUMAUHUNGCEKLDCEMLRUJSMLPRSQLP $.
$}

${
  $( A -> (B <-> C), A -> (C <-> D) |- A -> (B <-> D) $)
  bitrd.1 $e |- implies phi iff psi psi2 $.
  bitrd.2 $e |- implies phi iff psi2 chi $.
  bitrd $p |- implies phi iff psi chi $=
    ( logbinopimplies wff_logbinop logbinopiff bi2 syl imim2 mpd bi1 bi3 ) AGBC
    HZICBHZAGDCHZPAICDHZRFDCJKAGBDHZGPRHAIDBHZTEBDJKCDBLKMAGCBHZGQPHAGDBHZUBAUA
    UCEBDNKAGCDHZGUBUCHASUDFDCNKBDCLKMBCOKM $.
$}

${
  $( A -> (B <-> C) |- A -> (C <-> B) $)
  bicomd.1 $e |- implies phi iff psi chi $.
  bicomd $p |- implies phi iff chi psi $=
    ( logbinopiff wff_logbinop logbinopimplies bi1 bi2 bi3 syl mpd ) AECBFZEBCF
    ZDMGCBFZNBCHMGBCFGNOFBCICBJKLK $.
$}

${
  $( A -> (B1 <-> B2), A -> (C1 <-> C2) |- A -> ((B1 <-> C1) <-> (B2 <-> C2)) $)
  bibid.1 $e |- implies phi iff psi psi2 $.
  bibid.2 $e |- implies phi iff chi chi2 $.
  bibid $p |- implies phi iff iff psi chi iff psi2 chi2 $=
    ( logbinopimplies logbinopiff wff_logbinop logbinopand andL syl andR bicomd
    bitrd exp bi3 mpd ) AHICBJZIEDJZJZIUATJZAUATKUAAJZBCDUDAIDBJZAUALZFMUDDCEAU
    ANUDCEUDAIECJZUFGMOPPQAHUATJHUCUBJATUAKTAJZDEBUHBDUHAUEATLZFMOUHBECATNUHAUG
    UIGMPPQTUARMS $.
$}

${
  $d x y z s $.  $d x y z t $.  $d x y u $.
  $( 0 != S t $)
  pa_ax1_term $p |- not = 0 S t $=
    ( tzero tsucc binpred_equals wff_atom wff_not logbinopiff wff_logbinop
    eq-suc varx tvar eqeq2 syl notbi pa_ax1 var_to_term ) AJBJKZCZDEZFZBACZDEZFZQ
    ADEZGUBSHZGUCTHUDRUADEUEQAIRUABLMSUBNMJOP $.

  $( S s = S t -> s = t $)
  pa_ax2_term $p |- implies = S s S t = s t $=
    ( vary logbinopimplies binpred_equals wff_atom tsucc wff_logbinop
    logbinopiff varx tvar eq-suc eqeq2 syl imbid eqeq1 pa_ax2 var_to_term ) BCDAC
    KZEFZAGZSGZEFZHZDABEFZUABGZEFZHSBEFZUCTUGUEUHUBUFEFIUGUCHSBLUBUFUAMNSBAMOAJDJ
    KZSEFZUIGZUBEFZHUDUIAEFZULUJUCTUMUKUAEFIUCULHUIALUKUAUBPNUIASPOJCQRR $.

  $( s + 0 = s $)
  pa_ax3_term $p |- = + s 0 s $=
    ( varx tzero binop_plus tbinop binpred_equals wff_atom tvar eqeq1
    logbinopiff wff_logbinop logbinopand id logbinopimplies eq-refl ax-1 ax-mp
    andId eq-binop syl eqeq2 bitrd pa_ax3 var_to_term eq-sym ) AACDEZFGZUFAFGABBH
    ZUHCDEZFGZUGUHAFGZUJUGAUIFGZUHAUIIUKUIUFFGZJUGULKUKLCCFGZUKKUMUKUKUNUKMUNNUNU
    KKCOUNUKPQRUHACCDSTUIUFAUATUBBUCUDAUFUEQ $.

  $( s + S t = S (s + t) $)
  pa_ax4_term $p |- = + s S t S + s t $=
    ( vary varx binop_plus tbinop tsucc binpred_equals wff_atom tvar
    wff_logbinop logbinopiff logbinopand eqidd id andId eq-binop syl eq-suc eqeq1
    eqeq2 pa_ax4 bitrd var_to_term eq-sym ax-mp ) ABEFZGZABGZEFZHIZUJUHHIBCACJZEF
    ZGZAULGZEFZHIZUKULBHIZUQUKUHUPHIZURUNUHHIZLUSUQKURUMUGHIZUTURMURAAHIZKVAURVBU
    RAURNZUROPAAULBEQRUMUGSRUNUHUPTRURUPUJHIZLUKUSKURMUOUIHIZVBKVDURVBVEVCULBSPAA
    UOUIEQRUPUJUHUARUCADDJZULEFZGZVFUOEFZHIZUQVFAHIZVJUQUNVIHIZVKVHUNHIZLVLVJKVKV
    GUMHIZVMVKMULULHIZVKKVNVKVKVOVKOZULVKNPVFAULULEQRVGUMSRVHUNVITRVKVIUPHIZLUQVL
    KVKMUOUOHIZVKKVQVKVKVRVPUOVKNPVFAUOUOEQRVIUPUNUARUCDCUBUDUDUHUJUEUF $.

  $( s * 0 = 0 $)
  pa_ax5_term $p |- = * t 0 0 $=
    ( varx tzero binop_times binpred_equals wff_atom tvar logbinopiff
    logbinopand tbinop wff_logbinop eqidd andId eq-binop syl eqeq2 pa_ax5
    var_to_term eq-sym id ax-mp ) CACDJZEFZUBCEFABCBGZCDJZEFZUCUDAEFZUEUBEFZHUCUF
    KUGICCEFZUGKUHUGUGUIUGTCUGLMUDACCDNOUEUBCPOBQRCUBSUA $.

  $( s * S t = s * t + s $)
  pa_ax6_term $p |- = * s S t + * s t s $=
    ( vary varx binop_times tbinop binop_plus binpred_equals wff_atom
    logbinopiff tsucc tvar wff_logbinop logbinopand eqidd id andId eq-binop syl
    eqeq1 eq-suc eqeq2 bitrd pa_ax6 var_to_term eq-sym ax-mp ) ABEFZAGFZABKZEFZHI
    ZUKUIHIBCACLZEFZAGFZAUMKZEFZHIZULUMBHIZURULUIUQHIZUSUOUIHIZJUTURMUSNAAHIZUNUH
    HIZMVAUSVCVBUSNUSVBMVCUSVBUSAUSOZUSPQAAUMBERSVDQUNUHAAGRSUOUIUQTSUSUQUKHIZJUL
    UTMUSNUPUJHIZVBMVEUSVBVFVDUMBUAQAAUPUJERSUQUKUIUBSUCADDLZUMEFZVGGFZVGUPEFZHIZ
    URVGAHIZVKURUOVJHIZVLVIUOHIZJVMVKMVLNVLVHUNHIZMVNVLVOVLVLNUMUMHIZVLMVOVLVLVPV
    LPZUMVLOQVGAUMUMERSVQQVHUNVGAGRSVIUOVJTSVLVJUQHIZJURVMMVLNUPUPHIZVLMVRVLVLVSV
    QUPVLOQVGAUPUPERSVJUQUOUBSUCDCUDUEUEUIUKUFUG $.

  $( s < t <-> (E. x, t = s + S x) $)
  pa_ax7_term $p |- iff < s t exists x = t + s S x $=
    ( varz vary logbinopiff quant_ex binop_plus binpred_equals wff_atom
    wff_quant tvar tbinop binpred_less_than wff_logbinop logbinopand eqidd id
    andId syl tsucc eq-congr eqeq1 alpha_1 bibid eq-binop eqeq2 pa_ax7
    var_to_term ) BDFCGDLZACLUAZHMZIJZKZAUJNJZOZFCGBULIJZKZABNJZOUJBIJZUOUNUSURUT
    PUTAAIJZOFUSUOOUTVAUTAUTQUTRSAAUJBNUBTCGUTUMUQUJBULUCUDUEAEFCGUJELZUKHMZIJZKZ
    VBUJNJZOUPVBAIJZVFVEUOUNVGPUJUJIJZVGOFUOVFOVGVGVHVGRZUJVGQSVBAUJUJNUBTCGVGVDU
    MVGVCULIJZFUMVDOVGPUKUKIJZVGOVJVGVGVKVIUKVGQSVBAUKUKHUFTVCULUJUGTUDUEEDCUHUIU
    I $.
$}

${
  $( A -> (B1 <-> B2), A -> (C1 <-> C2) |- A -> ((B1 <-> C1) <-> (B2 <-> C2)) $)
  eqtri.1 $e |- = s t $.
  eqtri.2 $e |- = t u $.
  eqtri $p |- = s u $=
    ( logbinopand binpred_equals wff_atom wff_logbinop logbinopimplies eq-trans
    andI ax-mp ) FBCGHZABGHZIZACGHNPEOJPNIDONLMMABCKM $.
$}

2p2e4 $p |- = + S S 0 S S 0 S S S S 0 $=
  ( tzero tsucc binop_plus tbinop pa_ax4_term binpred_equals pa_ax3_term
  eq-suc wff_atom ax-mp eqtri ) ABZBZMCDMLCDZBZMBZBZMLENPFIOQFINMACDZBZPMAERMFI
  SPFIMGRMHJKNPHJK $.
