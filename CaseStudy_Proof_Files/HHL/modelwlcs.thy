theory modelwlcs_mjcs
imports HHL
begin

definition T :: exp where
"T == Real 0.01"
definition t :: exp where
"t == RVar ''t''"
definition h :: exp where
"h == RVar ''h''"
definition v :: exp where
"v == RVar ''v''"
consts Qmax :: exp
consts pi :: exp
consts g :: exp
consts r :: exp

consts con2plnt :: cname
consts plnt2con :: cname

definition x :: exp where
"x == RVar ''x''"
definition y :: exp where
"y == RVar ''y''"

definition cc ::exp where
"cc == SVar ''cc''"

definition assumVal::exp where
"assumVal == BVar ''tVal''"

definition conProp :: fform where
"conProp == (y[=](Real 0) [|] y[=](Real 1))"

definition inverT0 :: fform where
"inverT0 == t[>=](Real 0) [&] t[<=]T [&] (v[=](Real 1) [&] (h[>=](Real 0.30) [&] h[*](Real 1000)[<=](Real 590)[+](Real 3)[*]t) [|] (v[=](Real 0) [&] h[<=](Real 0.60) [&] h[*](Real 1000)[>=](Real 310) [-] (Real 7)[*]t))"
definition inverT1 :: fform where
"inverT1 == (v[=](Real 1) [&] (h[>=](Real 0.30) [&] h[<=](Real 0.59)) [|] (v[=](Real 0) [&] h[<=](Real 0.60) [&] h[>=](Real 0.31)))"
definition inverT2 :: fform where
"inverT2 == x[=]h [&] t[>=](Real 0) [&] t[<=]T [&] (v[=](Real 1) [&] (x[>=](Real 0.30) [&] x[*](Real 1000)[<=](Real 590)[+](Real 3)[*]t) [|] (v[=](Real 0) [&] x[<=](Real 0.60) [&] x[*](Real 1000)[>=](Real 310) [-] (Real 7)[*]t)) [&] conProp"
definition inverT3 :: fform where
"inverT3 == x[=]h [&] t[>=](Real 0) [&] t[<=]T [&] (v[=](Real 1) [&] (x[>=](Real 0.30) [&] x[*](Real 1000)[<=](Real 590)[+](Real 3)[*]t) [|] (v[=](Real 0) [&] x[<=](Real 0.60) [&] x[*](Real 1000)[>=](Real 310) [-] (Real 7)[*]t)) [&] ((y[=](Real 1) [|] x[>](Real 0.31))) [&] conProp"
definition inverT4 :: fform where
"inverT4 == x[=]h [&] t[>=](Real 0) [&] t[<=]T [&] (y[=](Real 1) [&] (x[>=](Real 0.30) [&] x[<=](Real 0.59)) [|] (y[=](Real 0) [&] x[<=](Real 0.60) [&] x[>=](Real 0.31))) [&] conProp"

definition assum :: fform where
"assum == assumVal [=](Bool True)[&] cc[=](String ''on'')[&] (t[=](Real 0)) [&] (h[=](Real 0.31)) [&] (v[=](Real 1))"
definition ensure :: fform where
"ensure == (h[>=](Real 0.30)) [&] (h[<=](Real 0.60))"
definition H :: fform where
"H == high (ensure)"

definition midCond0 :: "mid" where
"midCond0 == (inverT0, (high inverT0) [&] (l[=]T))"
definition midCond1 :: "mid" where
"midCond1 == (inverT1, (high inverT0) [&] (l[=]T))"
definition midCond2 :: "mid" where
"midCond2 == (conProp, (l[=]T))"
definition midCond3 :: "mid" where
"midCond3 == (inverT2, (l[=]T))"
definition midCond4 :: "mid" where
"midCond4 == (inverT3, (l[=](Real 0)))"
definition midCond5 :: "mid" where
"midCond5 == (inverT4, (l[=]T))"


definition WaterTank :: proc where
"WaterTank ==  (((<inverT0 && (t[<]T ) > : (l[=]T)) [[> (plnt2con !! h)); midCond0; (con2plnt ?? v)); midCond1; (t:=(Real 0))"

definition ControlCmd :: proc where
"ControlCmd ==(((<conProp && WTrue> : (l[=]T)); midCond2; plnt2con??x); midCond3; ((IF (x[<=](Real 0.31)) (y:=(Real 1))); midCond4; (IF (x[>=](Real 0.59)) (y:=(Real 0))))); midCond5; con2plnt!!y"

definition WLCS :: proc where
"WLCS == (WaterTank *) || (ControlCmd *)"

lemma "{assum, conProp} WLCS {ensure, conProp; H, WTrue}"
apply (simp add: WLCS_def)
apply (cut_tac px= "inverT0" and py="conProp" and qx="inverT0" and qy="conProp" and Hx="high inverT0 " and Hy="WTrue" in ConsequenceP,auto)
prefer 2
(*to inv*)
apply (rule conjR)
apply (rule Trans)
apply (simp add: assum_def inverT0_def v_def h_def t_def equal_greater_def equal_less_def T_def)
apply (rule conjR)
apply (rule Trans)
apply (simp add: assum_def inverT0_def v_def h_def t_def equal_greater_def equal_less_def)
apply (rule conjR)
apply (simp add: inverT0_def ensure_def)
apply (rule impR)
apply (rule conjL, rule conjL)
apply (rule disjL)
apply (rule conjR)
apply (rule Trans3)
apply (simp add: assum_def inverT0_def v_def h_def t_def equal_greater_def equal_less_def ensure_def T_def)
apply (rule conjL)+
apply (cut_tac P="v [=] Real 1" in thinL, auto)
apply (cut_tac P="h [>=] Real 3 / 10" in thinL, auto)
apply (rule Trans3)
apply (simp add: assum_def inverT0_def v_def h_def t_def equal_greater_def equal_less_def ensure_def T_def)
apply smt
apply (rule Trans3)
apply (simp add: assum_def inverT0_def v_def h_def t_def equal_greater_def equal_less_def ensure_def T_def)
apply smt
apply (rule conjR, rule impR, rule basic)
apply (rule conjR, rule impR)
apply (simp add: H_def)
apply (rule DC18)
apply (simp add: inverT0_def ensure_def)
apply (rule conjL, rule conjL)
apply (rule disjL)
apply (rule Trans3)
apply (simp add: assum_def inverT0_def v_def h_def t_def equal_greater_def equal_less_def ensure_def T_def)
apply smt
apply (rule Trans3)
apply (simp add: assum_def inverT0_def v_def h_def t_def equal_greater_def equal_less_def ensure_def T_def)
apply smt
apply (rule impR, rule basic)
(*rep*)
apply (rule Repetition)
defer
(*to inv*)
apply (rule impR)
apply (rule DCR3, rule basic)
apply (rule impR, rule thinL, rule Trans, simp)
(*one*)
apply (cut_tac px= "inverT0" and py="conProp" and qx="inverT0" and qy="conProp" and Hx="(high inverT0) [&] (l[=]T)" and Hy="WTrue [&] (l[=]T)" in ConsequenceP,auto)
prefer 2
apply (rule Trans, simp)
apply (simp add: WaterTank_def ControlCmd_def)
apply (rule Structure)
apply (simp add: midCond5_def midCond1_def)
apply (cut_tac Gy="l[=](Real 0)" in Parallel1a, auto)
defer
apply (rule Assign, auto)
apply (simp add: inverT0_def equal_greater_def equal_less_def)
apply (rule Trans)
apply (simp add: inverT1_def t_def inverT0_def assum_def inverT0_def v_def h_def t_def equal_greater_def equal_less_def T_def)
apply smt
apply (rule impR, rule LL4, rule basic)
(*comm1*)
apply (simp add: midCond0_def)
apply (rule Communication1, auto)
apply (simp add: inverT1_def equal_greater_def equal_less_def)
defer
apply (rule conjR, rule impR)
apply (simp add: inverT4_def)
apply (rule conjL)+
apply (rule basic)
apply (rule impR, rule conjL, cut_tac P="inverT0" in thinL, auto)
apply (simp add: inverT4_def inverT1_def v_def y_def h_def equal_greater_def equal_less_def x_def)
apply (rule conjL)+
apply (cut_tac P="t [>] Real 0 [|] t [=] Real 0" in thinL, auto)
apply (cut_tac P="t [<] T [|] t [=] T" in thinL, auto)
apply (cut_tac P="conProp" in thinL, auto)
apply (rule Trans2, simp)
apply (metis zero_neq_one)
apply (rule conjR, rule impR, rule thinL, rule Trans, simp)
apply (rule impR, rule LC1)
apply (rule DCL3)
apply (rule basic)
apply (rule Trans, simp)
(*ass*)
apply (rule Structure)
apply (simp add: midCond3_def)
apply (cut_tac Gy="l[=](Real 0)" in Parallel1a, auto)
defer
apply (cut_tac px="inverT2" and qx="inverT4" and Hx="(l[=](Real 0))[^](l[=](Real 0))" in ConsequenceS, auto)
apply (simp add: midCond4_def)
apply (rule Sequence)
apply (cut_tac b="(x [<=] Real 31 / 100)" in Case, auto)
apply (rule ConditionT)
apply (rule Trans, simp)
apply (rule Assign, auto)
apply (simp add: inverT3_def conProp_def equal_greater_def equal_less_def)
apply (rule conjR)
apply (simp add: x_def y_def inverT2_def inverT3_def equal_greater_def equal_less_def t_def T_def h_def v_def)
apply (rule impR)
apply (rule conjL)+
apply (rule conjR, rule basic)+
apply (rule thinL)+
apply (rule Trans, simp add: conProp_def y_def)
apply (rule impR, rule basic)
apply (rule ConditionF)
apply (rule Trans, simp)
apply (simp add: x_def y_def inverT2_def inverT3_def equal_greater_def equal_less_def t_def T_def h_def v_def)
apply (rule impR)
apply (rule conjL)+
apply (rule conjR, rule basic)+
apply (rule thinL, rule thinL, rule thinL, rule thinL)
apply (rule conjR, rule thinL)
apply (rule disjR, rule thinR)
apply (rule Trans1, simp)
apply (rule basic)
apply (rule impR, rule basic)
apply (cut_tac b="(x [>=] Real 59 / 100)" in Case, auto)
apply (rule ConditionT)
apply (rule Trans, simp)
apply (rule Assign, auto)
apply (simp add: inverT4_def conProp_def equal_greater_def equal_less_def)
apply (rule conjR)
apply (simp add: inverT3_def inverT4_def equal_greater_def equal_less_def t_def T_def h_def v_def y_def x_def conProp_def)
apply (rule Trans, simp)
apply smt
apply (rule impR, rule basic)
apply (rule ConditionF)
apply (rule Trans, simp)
apply (simp add: inverT3_def inverT4_def)
apply (rule impR)
apply (rule conjL)+
apply (rule conjR, rule basic)+
apply (rule conjR)
apply (cut_tac P="x [>=] Real 3 / 10" in cut, auto)
apply (rule thinR)
apply (rule thinL, rule thinL)
apply (cut_tac P="conProp" in thinL, auto)
apply (rule Trans4)
apply (simp add: inverT3_def inverT4_def equal_greater_def equal_less_def t_def T_def h_def v_def y_def x_def)
apply smt
apply (rule thinL, rule thinL, rule thinL, rule thinL)
apply (rule Trans4, simp add: conProp_def x_def y_def equal_greater_def equal_less_def)
apply metis
apply (rule basic)
apply (rule impR, rule basic)
apply (rule conjR, rule impR, rule basic)+
apply (rule impR, rule LL4, rule basic)+
(*comm2*)
apply (simp add: midCond2_def)
apply (cut_tac Hy="l[=]T" and H="l[=]T" and pre="inverT0" and Init="WTrue" in CommunicationI1b, auto) 
apply (simp add: inverT2_def conProp_def equal_greater_def equal_less_def)
apply (rule impR, rule basic)
apply (rule impR, rule RL3)
apply (cut_tac R=WTrue in CMR, auto)
apply (rule basic)
apply (rule thinL, rule Trans, simp)
apply (cut_tac px="conProp [&] WTrue" and qx="conProp" and Hx="l [=] T" in ConsequenceS, auto)
apply (rule Continue)
prefer 6
apply (simp add: inverT3_def inverT4_def equal_greater_def equal_less_def t_def T_def h_def v_def y_def x_def)
apply (simp add: inverT2_def inverT0_def equal_greater_def equal_less_def t_def T_def h_def v_def y_def x_def)
apply (rule impR)
apply (rule conjL)+
apply (rule conjR)
apply (rule thinL)+
apply (rule Trans, simp)
apply (rule conjR, rule basic)+
apply (simp add: conProp_def y_def, rule basic)
prefer 6
apply (rule impR)
apply (rule conjL)+
apply (rule disjL)
apply (rule Trans2, simp add: ltrans T_def)
apply (metis mult_zero_left zero_neq_one)
apply (rule conjR)
apply (cut_tac P="l[=]T" in thinL, auto)
apply (rule DC18)
apply (rule conjL)+
apply (rule basic)+
apply (rule Trans, simp add: conProp_def)+
done

end
