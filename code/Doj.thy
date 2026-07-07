(*<*)
theory Doj
  imports Main "HOL.Rat" "HOL-Library.LaTeXsugar"  "HOL-Probability.Probability"  base
begin
(*>*)
declare [[quick_and_dirty = true]]


abbreviation fact :: "literal \<Rightarrow> argument" 
  where "fact l \<equiv> ({},l)"

(* Isar Ref. S. 277 *)
text \<open>Wir definieren den Typen ccPosition als eine Position, die complete und konsistent ist.\<close>
typedef \<Omega> = "{P :: position. consistent P \<and> complete P}"
   using consistent_def complete_def literal.sel(1) 
   by (metis literal.disc(1) literal.disc_eq_case(2) literal.simps(6) mem_Collect_eq)
definition \<Omega> where "\<Omega> = (UNIV :: \<Omega> set)"

text \<open>Ein Argument hat die Form einer Implikation. Wenn die Prämissen in der Position enthalten sind,
erfüllt die Position das Argument, wenn die Konklusion ebenfalls entfalten ist. Wenn die Position
das Komplement einer Prämisse enthält, erfüllt die Position ebenfalls das Argument.
\#Info Wenn die Position dem Argument erfüllt, dann modelliert die Interpretation P das Argument\<close>
fun models_arg :: "position \<Rightarrow> argument \<Rightarrow> bool" (infix "\<Turnstile>\<^sub>a" 65)
  where "models_arg P (ps,c) = (ps \<subseteq>  P \<longrightarrow> c \<in>  P)"

text \<open>Eine vollständig und konsistente Position ist kohärent, wenn sie alle Argumente
der Debatte erfüllt.\<close>
definition coherent :: "\<Omega> \<Rightarrow> ds \<Rightarrow> bool"  (infix "\<Turnstile>" 65)
  where "coherent P ds = (\<forall>A \<in> ds . models_arg (Rep_\<Omega> P) A)"

definition satisfiable :: "ds \<Rightarrow> bool"
  where "satisfiable ds = (\<exists>P . P \<Turnstile> ds)"

text \<open>Die Positionen sind endlich\<close>
lemma finite_positions:  "finite (UNIV :: position)"
(*<*)
proof -
  have "((UNIV :: literal set) = range Pos \<union> range Neg)"
    by (metis literal.exhaust UNIV_eq_I Un_iff rangeI)
  thus ?thesis
    using finsen by (metis finite_Un finite_imageI)
qed
(*>*)

text \<open>Der Grundraum ist endlich => Wir befinden uns im diskreten Fall\<close>
lemma \<Omega>_fin: "finite \<Omega>"
(*<*)
  using finite_positions \<Omega>_def
  by (metis (full_types) Finite_Set.finite_set Rep_\<Omega>_inverse UNIV_I
      ex_new_if_finite finite_imageI image_eqI)
(*>*)


text \<open>Wir definieren @{term "\<omega>"} als Untermenge von @{term "\<Omega>"}, sodass alle @{term "p \<in> \<omega>"} zusätzlich die Debatte erfüllen.
Das sind alle Modelle der Debatte.\<close>
definition \<omega> :: "ds \<Rightarrow> \<Omega> set"
  where "\<omega> ds = {p \<in> \<Omega> . p \<Turnstile> ds}"

(*<*)
lemma \<omega>_fin: "finite (\<omega> ds)" using \<Omega>_fin 
  using \<Omega>_def rev_finite_subset by auto
(*>*)

text \<open>Wir definieren die Wahrscheinlichkeitsfunkion bzw. Dichte als Gleichverteilung.
Dabei werden alle nicht kohärenten Positionen nicht betrachtet. (of\_bool ist definiert als @{term "if P \<Turnstile> ds then 1 else 0"})\<close>

definition f :: "\<Omega> \<Rightarrow> real"
  where "f P =  (1 / card \<Omega>)"

text \<open>Damit ist Pr ganz kanonisch genau das diskrete Wahrscheinlichkeitsmaß bzgl. f\<close>
definition Pr :: "\<Omega> set \<Rightarrow> real"
  where "Pr Ps = (\<Sum> p \<in> Ps. f p)"

text \<open>Die bedingte Wahrscheinlichkeit ist folgendermaßen definiert.\<close>
definition Pr_cond 
  where "Pr_cond H E = Pr (H \<inter> E) / Pr E"

definition ext :: "position \<Rightarrow> \<Omega> set" 
  where "ext P = {x \<in> \<Omega> . P \<subseteq> Rep_\<Omega> x}"

lemma ext_\<omega>: "ext P = \<omega> (image fact P)"
  using ext_def \<omega>_def coherent_def by auto

lemma ext_\<omega>2: "ext P = \<omega> ({({}, l) | l. l \<in> P })"
  using ext_def \<omega>_def coherent_def by auto

lemma ext_fin: "finite (ext P)" using ext_\<omega> \<omega>_fin by presburger


lemma pr_card: 
  assumes "satisfiable ds"
  shows "Pr_cond (ext P) (\<omega> ds) = card ((ext P) \<inter> \<omega> ds) / card (\<omega> ds)"
unfolding Pr_cond_def Pr_def f_def using \<omega>_fin ext_fin assms 
  using \<Omega>_def \<Omega>_fin by auto

(* 
text \<open>doj lässt sich damit sehr einfach über Pr definieren.\<close>
definition doj :: "ds \<Rightarrow> position \<Rightarrow> real"
  where "doj ds P = Pr ds (ext P)"

text \<open>Bedingte doj lassen sich über Pr_cond definieren.\<close>
definition doj_cond :: "ds \<Rightarrow> position \<Rightarrow> position \<Rightarrow> real"
  where "doj_cond ds P B = Pr_cond ds (ext P) (ext B)" *)



text \<open>Die Brücke zu HOL-Probability\<close>
abbreviation prob where "prob \<equiv> measure_pmf.prob (pmf_of_set \<Omega>)"

lemma pr_prob_eq [simp]: "Pr P = prob P" 
proof -
have "\<forall>x . (pmf (pmf_of_set \<Omega>)) x = f x"
using pmf_of_set f_def \<omega>_fin \<omega>_def \<Omega>_def 
  by (metis UNIV_I \<Omega>_fin empty_iff indicator_UNIV)
  thus ?thesis using Pr_def \<Omega>_def \<Omega>_fin infinite_super measure_measure_pmf_finite subset_UNIV sum.cong
    by metis
qed

lemma between0_1: 
"0 \<le> Pr A \<and> Pr A \<le>1" using pr_prob_eq by simp


lemma bayes:
  shows "Pr_cond A B = Pr_cond B A * Pr A / Pr B"
    using  Pr_cond_def pr_prob_eq inf_commute 
    by (metis \<Omega>_def \<Omega>_fin inf_bot_right inf_top.right_neutral measure_pmf_zero_iff mult_eq_0_iff
        nonzero_eq_divide_eq set_pmf_of_set)

lemma cond_mult: "Pr (A \<inter> B) = Pr_cond A B * Pr B" unfolding Pr_cond_def pr_prob_eq 
  by (simp add: inf_left_commute measure_pmf_zero_iff)

lemma bayes_two:
  shows "Pr_cond A (B \<inter> C) = Pr_cond C (A \<inter> B) * Pr_cond A B  / Pr_cond C B"
  unfolding Pr_cond_def using pr_prob_eq 
  by (smt (verit, ccfv_threshold) cond_mult divide_divide_eq_right divide_eq_0_iff inf_aci(3)
      inf_sup_aci(1) nonzero_eq_divide_eq)

lemma \<omega>_inter: "\<omega> (ds1 \<union> ds2) = (\<omega> ds1) \<inter> (\<omega> ds2)" using \<omega>_def coherent_def by auto

lemma extended_subset: "\<omega> (ds1 \<union> ds2) \<subseteq> \<omega> ds1" 
proof 
  fix x
  assume "x \<in> \<omega> (ds1 \<union> ds2)"
  thus "x \<in>  \<omega> ds1" 
    using \<omega>_def coherent_def consistent_def complete_def by simp
qed


definition entailment ::  "ds \<Rightarrow>  ds \<Rightarrow> bool" (infix "\<Turnstile>\<^sub>e" 50)
  where "entailment ds1 ds2 = (\<omega> ds1 \<subseteq> \<omega> ds2)"

lemma "(ds1 \<union> ds2) \<Turnstile>\<^sub>e ds1" 
  using entailment_def extended_subset by simp


find_theorems "card" "times"
find_theorems "bij" "card"
find_theorems "card" "inter" "times"

lemma normal_subset_if_fullfills:
  assumes "\<forall>Q \<in> \<omega> ds1 . Q \<Turnstile> ds2"
  shows "\<omega> ds1 \<subseteq> \<omega> (ds1 \<union> ds2)"
(*<*)
proof
  fix x 
  assume "x \<in> \<omega> ds1"
  thus "x \<in>  \<omega> (ds1 \<union> ds2)" using \<omega>_def coherent_def 
complete_def consistent_def assms by fastforce
qed

lemma s:
  assumes "\<omega> ds1 \<subseteq> \<omega> (ds1 \<union> ds2)"
  shows "\<forall>Q \<in> \<omega> ds1 . Q \<Turnstile> ds2"
using \<omega>_def coherent_def 
complete_def consistent_def assms by auto

lemma \<omega>_eq: "\<omega> ds1 = \<omega> (ds1 \<union> ds2) \<longleftrightarrow> ds1 \<Turnstile>\<^sub>e (ds2 \<union> ds1)"
  using s normal_subset_if_fullfills entailment_def 
  by (simp add: \<omega>_inter inf.order_iff sup.commute)


lemma "\<omega> {} = \<Omega>" using \<omega>_def \<Omega>_def coherent_def by simp


fun split_mods :: "ds \<Rightarrow> ds \<Rightarrow> \<Omega>  \<Rightarrow> (\<Omega> \<times> \<Omega>)"
where "split_mods ds1 ds2 x = (Abs_\<Omega> {l \<in> Rep_\<Omega> x . sen l \<in> domain_ds ds1}, Abs_\<Omega> {l \<in> Rep_\<Omega> x . sen l \<in> domain_ds ds2})"

lemma card_ind_mods: 
  assumes "domain_ds ds1 \<inter> domain_ds ds2 = {}"
  shows "card (\<omega> (ds1 \<union> ds2)) = card (\<omega> ds1) * card (\<omega> ds2)"
proof -
  let ?f = "\<lambda>x \<in> \<Omega> . ({l \<in> Rep_\<Omega> x . sen l \<in> domain_ds ds1}, {l \<in> Rep_\<Omega> x . sen l \<in> domain_ds ds2})"
  have "bij_betw (split_mods ds1 ds2) (\<omega> (ds1 \<union> ds2)) ((\<omega> ds1) \<times> (\<omega> ds2))"
  proof (rule bij_betw_imageI)
    show "inj_on (split_mods ds1 ds2) (\<omega> (ds1 \<union> ds2))" sorry
    show "split_mods ds1 ds2 ` \<omega> (ds1 \<union> ds2) = \<omega> ds1 \<times> \<omega> ds2" 
    proof (intro antisym)
      show "split_mods ds1 ds2 ` \<omega> (ds1 \<union> ds2) \<subseteq> \<omega> ds1 \<times> \<omega> ds2"  
        using assms bij_betw_def \<omega>_def coherent_def \<Omega>_fin split_mods.simps card_PiE bij_betw_disjoint_Un sorry
      show "\<omega> ds1 \<times> \<omega> ds2 \<subseteq> split_mods ds1 ds2 ` \<omega> (ds1 \<union> ds2)" sorry
    qed
  qed

  hence "card (\<omega> (ds1 \<union> ds2)) = card (\<omega> ds1 \<times> \<omega> ds2)" using bij_betw_same_card by fast
  thus ?thesis using card_cartesian_product by simp
qed





definition propto :: "real \<Rightarrow> real \<Rightarrow> bool" (infix "\<propto>" 50) where
  "x \<propto> y \<longleftrightarrow> (\<exists> c \<ge> 0. x = c * y)"


lemma extended_ds_diff:
  shows "(Pr_cond (ext P)(\<omega> (ds1 \<union> ds2)) - Pr_cond (ext P) (\<omega> ds1)) 
       \<propto> (Pr_cond (\<omega> ds2) (ext P \<inter> \<omega> ds1) / Pr_cond (\<omega> ds2) (\<omega> ds1)) -1"
proof -
  let ?X = "ext P"
  let ?D1 = "\<omega> ds1"
  let ?D2 = "\<omega> ds2"

  have "Pr_cond ?X (\<omega> (ds1 \<union> ds2)) - Pr_cond ?X ?D1 = Pr_cond ?X (?D1 \<inter> ?D2) - Pr_cond ?X ?D1" using \<omega>_inter by simp
  also have "... = Pr_cond ?D2 (?X \<inter> ?D1) / Pr_cond ?D2 ?D1 * Pr_cond ?X ?D1 - Pr_cond ?X ?D1" using bayes_two 
    by (metis times_divide_eq_left)
  finally have "... = Pr_cond ?X ?D1 * (Pr_cond ?D2 (?X \<inter> ?D1) / Pr_cond ?D2 ?D1 - 1)" by argo
  thus ?thesis using propto_def 
    by (metis \<omega>_inter
        \<open>Pr_cond (ext P) (\<omega> ds1 \<inter> \<omega> ds2) - Pr_cond (ext P) (\<omega> ds1) = Pr_cond (\<omega> ds2) (ext P \<inter> \<omega> ds1) / Pr_cond (\<omega> ds2) (\<omega> ds1) * Pr_cond (ext P) (\<omega> ds1) - Pr_cond (ext P) (\<omega> ds1)\<close>
        bayes between0_1 cond_mult divide_nonneg_nonneg)
qed

lemma [simp]:
  assumes "satisfiable ((image fact P) \<union> ds1)"
  shows "card (\<omega> ((image fact P) \<union> ds1)) > 0" using satisfiable_def \<omega>_def 
  using \<Omega>_def \<omega>_fin assms card_gt_0_iff by blast


lemma "ext {Pos s} \<union> ext {Neg s} = \<Omega>"
proof
  show "ext {Pos s} \<union> ext {Neg s} \<subseteq> \<Omega>" using ext_def by blast
  show " \<Omega> \<subseteq> ext {Pos s} \<union> ext {Neg s}" 
  proof 
    fix x 
    assume "x \<in> \<Omega>"
    thus "x \<in> ext {Pos s} \<union> ext {Neg s}" 
     proof (cases "(Pos s) \<in> Rep_\<Omega> x")
        case True
        then show ?thesis 
          using ext_def 
          by (simp add: \<Omega>_def)
      next
        case False
        then have "Neg s \<in> Rep_\<Omega> x"
          using \<Omega>_def consistent_def 
          by (metis Rep_\<Omega> base.complete_def literal.exhaust_sel mem_Collect_eq)
        then show ?thesis 
          using ext_def \<Omega>_def by simp
      qed
  qed
qed

lemma "ext {Pos s} \<inter> ext {Neg s} = {}"
proof 
  show "{} \<subseteq> ext {Pos s} \<inter> ext {Neg s} " by simp
next
  show "ext {Pos s} \<inter> ext {Neg s} \<subseteq> {} "
 proof
  fix x
  assume "x \<in> ext {Pos s}  \<inter> ext {Neg s}"
  hence hpos: "x \<in> ext {Pos s}" 
    and hneg: "x \<in> ext {Neg s}" by auto
  have "x \<notin> ext {Neg s}" 
    using hpos coherent_def ext_def consistent_def 
    using Rep_\<Omega> by fastforce
  thus "x \<in> {}" using hneg by contradiction
qed
qed
  




lemma likelihood_eq1:
  assumes "satisfiable ((image fact P) \<union> ds1)"
  assumes "((image fact P) \<union> ds1) \<Turnstile>\<^sub>e (ds2 \<union> (image fact P) \<union> ds1)"
  shows "Pr_cond (\<omega> ds2) (ext P \<inter> \<omega> ds1) = 1 "
proof -
  have mod_eq: "\<omega> (ds2 \<union> (image fact P) \<union> ds1) = \<omega> ((image fact P) \<union> ds1)"
  proof (intro antisym)
    show "\<omega> (fact ` P \<union> ds1) \<subseteq> \<omega> (ds2 \<union> fact ` P \<union> ds1)" using assms entailment_def by metis
    show " \<omega> (ds2 \<union> fact ` P \<union> ds1)  \<subseteq> \<omega> (fact ` P \<union> ds1)" using extended_subset 
      using \<omega>_inter by force
  qed

  have "ext P = \<omega> (image fact P)" using ext_\<omega> by simp
  hence "Pr_cond (\<omega> ds2) (ext P \<inter> \<omega> ds1) = Pr_cond (\<omega> ds2) (\<omega> (image fact P) \<inter> (\<omega> ds1))" using \<omega>_inter by simp
  also have "... = Pr (\<omega> ds2 \<inter> \<omega> (image fact P) \<inter> (\<omega> ds1)) / Pr (\<omega> (image fact P) \<inter> (\<omega> ds1))" 
    unfolding Pr_cond_def by (simp add: inf_assoc)
  also have "... = card (\<omega> ds2 \<inter> \<omega> (image fact P) \<inter> \<omega> ds1) / card (\<omega> (image fact P) \<inter> (\<omega> ds1))" 
    using \<omega>_fin Pr_def Pr_cond_def \<Omega>_def \<Omega>_fin f_def by auto
  also have "... =  card (\<omega> (ds2 \<union> (image fact P) \<union> ds1)) / card (\<omega> ((image fact P) \<union> ds1))" using \<omega>_inter by presburger
  also have "... = 1" using mod_eq assms by simp
  finally show ?thesis using assms by satx
qed

lemma likelihood_sat:
  assumes "\<not> (satisfiable (ds2 \<union> (image fact P) \<union> ds1))"
  shows "\<omega> (ds2 \<union> (image fact P) \<union> ds1) = {}"
  using assms \<omega>_def satisfiable_def by auto


lemma sat_impl_card_nn: "satisfiable ds \<Longrightarrow> card (\<omega> ds) > 0"
  using \<omega>_def satisfiable_def \<omega>_fin \<Omega>_def card_gt_0_iff by fastforce

lemma sat_un:
assumes "satisfiable (ds1 \<union> ds2)"
shows "satisfiable ds1" and "satisfiable ds2"
using assms satisfiable_def by (meson UnCI coherent_def)+



lemma Pr_to_cond:
assumes "satisfiable ds1"
shows "Pr (ds1 \<union> ds2) Ps = Pr_cond ds1 Ps (\<omega> ds2)"
proof -

let ?H = "(\<omega> ds2)"

have "Pr_cond ds1 Ps ?H = Pr ds1 (Ps \<inter> ?H) / Pr ds1 ?H" using Pr_cond_def by simp
also have "... = (1 / real (card (\<omega> ds1)) * (\<Sum> P \<in> (Ps \<inter> ?H) .indicator (\<omega> ds1) P))
                /(1 / real (card (\<omega> ds1)) * (\<Sum> P \<in> ?H .indicator (\<omega> ds1) P))"  
  unfolding Pr_def f_def by (simp add: sum_distrib_left)
also have "... = (\<Sum> P \<in> (Ps \<inter> ?H) .indicator (\<omega> ds1) P) / (\<Sum> P \<in> ?H .indicator (\<omega> ds1) P)"
  using sat_impl_card_nn assms by simp
also have "... =  (\<Sum> P \<in> (Ps \<inter> ?H) .indicator (\<omega> ds1) P) / card (\<omega> (ds1 \<union> ds2))"
  proof - 
    have "(\<Sum> P \<in> ?H .indicator (\<omega> ds1) P) = card ((\<omega> ds1) \<inter> ?H)"
      using \<omega>_def by (metis \<Omega>_def \<Omega>_fin finite_subset inf_sup_aci(1) sum_indicator_eq_card top.extremum) 
    thus  ?thesis using \<omega>_inter by (metis (mono_tags, lifting) of_nat_sum real_of_nat_indicator sum.cong)
  qed
also have "... = (1 / card (\<omega> (ds1 \<union> ds2))) * (\<Sum> P \<in> (Ps \<inter> ?H) .indicator (\<omega> ds1) P)" by algebra
also have "... = (1 / card (\<omega> (ds1 \<union> ds2))) * (\<Sum> P \<in> Ps  .indicator (\<omega> (ds1 \<union> ds2)) P)"
  proof - 
    have "\<omega> (ds1 \<union> ds2) = (\<omega> ds1) \<inter> ?H" using \<omega>_def coherent_def by auto
    hence "(\<Sum> P \<in> (Ps \<inter> ?H) .indicator (\<omega> ds1) P) = (\<Sum> P \<in> Ps  .indicator (\<omega> (ds1 \<union> ds2)) P)"
        using \<omega>_def \<Omega>_def \<Omega>_fin finite_subset
    by (smt (verit, best) Diff_iff Int_iff indicator_simps(1,2) subset_eq sum.mono_neutral_cong_right top.extremum)  
    thus ?thesis by auto
  qed
also have "... = Pr (ds1 \<union> ds2) Ps" unfolding Pr_def f_def by (rule sum_distrib_left)
finally show ?thesis by auto
qed


lemma move_norm [simp]: "Pr ds P =  (1 / (card (\<omega> ds))) * sum (indicator (\<omega> ds)) P" 
  unfolding Pr_def f_def by (simp add: sum_distrib_left)

lemma pr_card [simp]: "Pr ds P = (1 / (card (\<omega> ds))) * card (\<omega> ds \<inter> P)" 
proof -
  have "finite P" using  \<Omega>_fin \<Omega>_def using rev_finite_subset by auto
  hence "sum (indicator (\<omega> ds)) P = card (\<omega> ds \<inter> P)" using sum_indicator_eq_card 
    by (metis inf_sup_aci(1))
  thus ?thesis using move_norm by (metis of_nat_sum real_of_nat_indicator sum.cong)
qed





lemma sat_union_deb_impl_Pr_gt0:
  assumes "satisfiable (ds1 \<union> ds2)"
  shows "Pr ds1 (\<omega> ds2) > 0" 
  using assms sat_un
    by (metis Pr_cond_def Pr_to_cond div_by_0 fix_ds.intro fix_ds.pr_prob_eq measure_pmf.prob_space_axioms one_neq_zero prob_space.prob_space zero_less_measure_iff)

lemma independence_eq [simp]: 
  assumes "Pr ds B > 0"
  shows "Pr_cond ds A B = Pr ds A \<longleftrightarrow> Pr ds (A \<inter> B) = Pr ds A * Pr ds B"
  using Pr_cond_def assms divide_eq_eq by (metis rel_simps(70))


text \<open>Monotonie für erweiterte Debatten ist probabilistische Relevanz der neuen Debatte für eine Position in der alten Debatte\<close>
theorem extends_prob_relevency_iff:
  assumes "satisfiable ds1"
  shows "doj (ds1 \<union> ds2) P - doj ds1 P = Pr_cond ds1 (ext P) (\<omega> ds2) - Pr ds1 (ext P)"
  using doj_def  Pr_to_cond assms by simp


lemma subset_args:  "\<forall>Ai \<in> ds . (\<Inter> A \<in> ds . \<omega> {A}) \<subseteq> \<omega> {Ai}"
  using \<omega>_inter by blast

lemma pr_to_args:
  assumes "satisfiable ds"
  shows "Pr ds P = Pr {} (P \<inter> (\<Inter> A \<in> ds . \<omega> {A})) / Pr {}  (\<Inter> A \<in> ds .  \<omega> {A})"
proof -
  have "\<forall>A \<in> ds . satisfiable {A}" using coherent_def satisfiable_def assms by auto
  hence "\<forall>A \<in> ds. \<omega> {A} \<noteq> {}" using \<omega>_def satisfiable_def by (metis card_gt_0_iff sat_impl_card_nn)
  hence "\<omega> ds = (\<Inter> A \<in> ds . \<omega> {A})" using \<omega>_def coherent_def 
    using \<Omega>_def by auto
  moreover have  "Pr ds P = Pr_cond {} P (\<omega> ds)" using Pr_to_cond 
    by (metis Un_empty_left assms sat_un(1))
  ultimately show ?thesis using Pr_cond_def by presburger
qed

lemma 
  assumes "satisfiable ds"
  assumes "ds \<noteq> {}"
  assumes "finite ds"
  shows "card (P \<inter> (\<Inter> A \<in> ds . \<omega> {A})) \<le> Min {card (P \<inter> \<omega> {A}) | A. A \<in> ds}"
proof -

  let ?A = "{card (\<omega> {A} \<inter> P) | A. A \<in> ds}"
  have "\<forall>Ai \<in> ?A . card (P \<inter> (\<Inter> A \<in> ds . \<omega> {A})) \<le> Ai" 
    using subset_args \<omega>_fin card_mono 
      by (smt (verit) Int_iff Set.basic_monos(7) finite_Int mem_Collect_eq subsetI)
  moreover have "?A \<noteq> {}" using assms by blast
  moreover have "finite ?A" using assms 
    by (smt (verit, del_insts) \<Omega>_def \<Omega>_fin card_mono finite_nat_set_iff_bounded_le mem_Collect_eq
        top_greatest)
  ultimately show ?thesis using Min_ge_iff 
    by (metis (no_types, lifting) ext inf_sup_aci(1))
qed

lemma Pr_cond_eq1:
  assumes "\<forall>x \<in> (ext P \<inter> \<omega> ds1) . x \<Turnstile> ds2"
  assumes "satisfiable ds1"
  assumes "Pr ds1 (ext P) > 0"
  shows "Pr_cond ds1 (\<omega> ds2) (ext P) = 1"
proof -
  have nn_gt0: "card ((\<omega> ds1) \<inter> (ext P)) > 0" using assms by (metis Num.of_nat_simps(1) of_nat_less_0_iff pr_card zero_less_mult_iff zero_order(5))

  have "(\<omega> (ds1 \<union> ds2)) \<inter> (ext P) = (\<omega> ds1) \<inter> (ext P)" 
  proof (intro antisym)
    show "\<omega> (ds1 \<union> ds2) \<inter> ext P \<subseteq> \<omega> ds1 \<inter> ext P" using extended_subset by blast
    show "\<omega> ds1 \<inter> ext P \<subseteq> \<omega> (ds1 \<union> ds2) \<inter> ext P" using normal_subset_if_fullfills assms try
      using \<omega>_def \<omega>_inter by auto
  qed
  hence "card ((\<omega> (ds1 \<union> ds2)) \<inter> (ext P)) = card ((\<omega> ds1) \<inter> (ext P))" by presburger
  hence "1 = (card ((\<omega> (ds1 \<union> ds2)) \<inter> (ext P)) / card ((\<omega> ds1) \<inter> (ext P)))" using nn_gt0 by simp
  thus ?thesis using pr_card 
    by (metis Pr_cond_def \<omega>_inter assms(3) divide_eq_eq_1 inf_sup_aci(2) order.strict_implies_not_eq)
qed

lemma Pr_cond_e0:
  assumes "\<forall>x \<in> (ext P \<inter> \<omega> ds1) . \<not>(x \<Turnstile> ds2)"
  assumes "satisfiable ds1"
  shows "Pr_cond ds1 (\<omega> ds2) (ext P) = 0"
proof -
  have "\<omega> (ds1 \<union> ds2) \<inter> (ext P) = {}" using assms 
    using \<omega>_def \<omega>_inter by auto
  hence "card ((\<omega> (ds1 \<union> ds2)) \<inter> (ext P)) = 0" by simp
  thus ?thesis using pr_card assms 
    by (metis (lifting) Multiseries_Expansion.intyness_0 Pr_cond_def
        \<omega>_inter divide_divide_eq_right division_ring_divide_zero inf_aci(3)
        inf_sup_aci(1))
qed
lemma 
  assumes "satisfiable ds1"
  assumes "Pr ds1 (ext P) > 0"
  assumes "Pr ds1 (\<omega> ds2) > 0"
  shows "doj (ds1 \<union> ds2) P - doj ds1 P \<propto>
        card (\<omega> ds1) * card ((\<omega> (ds1 \<union> ds2)) \<inter> ext P) - card (\<omega> (ds1 \<union> ds2)) * card (\<omega> ds1 \<inter> ext P)"
proof -

  let ?P = "ext P"
  let ?D = "\<omega> ds2"
  have gt0: "card (\<omega> ds1) > 0" using assms sat_impl_card_nn by simp

  interpret fix_ds ds1 using assms by unfold_locales
  let ?l1 = "(1 / prob ?D)"
  let ?l2 = "(1 / card (\<omega> ds1))^2"
  have "doj (ds1 \<union> ds2) P - doj ds1 P = Pr_cond ds1 ?P ?D - Pr ds1 ?P" using extends_prob_relevency_iff assms by presburger
  have "... = prob_cond ?P ?D - prob ?P" using pr_prob_eq unfolding Pr_cond_def by simp
  also have "... = (1 / prob ?D) * prob (?P \<inter> ?D) - prob ?P" by simp
  also have "... = (1 / prob ?D) * (prob (?P \<inter> ?D) - prob ?P * prob ?D)" using assms(3) pr_prob_eq 
    by (simp add: right_diff_distrib)
  also have "... = ?l1 * (prob (?P \<inter> ?D) - prob ?P * prob ?D)" using assms(3) propto_def 
    by simp
  also have "... =?l1 * (1 / card (\<omega> ds1)) * card (?P \<inter>?D \<inter> \<omega> ds1) - 
                   (1 / card (\<omega> ds1)) * card (?D \<inter> \<omega> ds1) * (1 / card (\<omega> ds1)) * card (?P \<inter> \<omega> ds1)" 
    using pr_card pr_prob_eq sorry

  also have "... =?l1 * (1 / card (\<omega> ds1)) * card (?P \<inter>?D \<inter> \<omega> ds1) - 
                   (1 / card (\<omega> ds1))^2 * card (?D \<inter> \<omega> ds1) * card (?P \<inter> \<omega> ds1)" by algebra
  also have "... = ?l1 * (1 / card (\<omega> ds1)) * (card (?P \<inter>?D \<inter> \<omega> ds1) - (1 / card (\<omega> ds1)) * card (?D \<inter> \<omega> ds1) * card (?P \<inter> \<omega> ds1))"
    using gt0 sorry
  also have "... =?l1 * (1 / card (\<omega> ds1)) * (card (?P \<inter>?D \<inter> \<omega> ds1) * card (\<omega> ds1) * (1 / card (\<omega> ds1))  - (1 / card (\<omega> ds1)) * card (?D \<inter> \<omega> ds1) * card (?P \<inter> \<omega> ds1))"
    using gt0 by auto
  also have "... = ?l1 * ?l2 * (card (?P \<inter>?D \<inter> \<omega> ds1) * card (\<omega> ds1) - card (?D \<inter> \<omega> ds1) * card (?P \<inter> \<omega> ds1))"
    sorry
  also have "... = ?l1 * ?l2 * card (\<omega> ds1) * card ((\<omega> (ds \<union> ds2)) \<inter> ext P) - card (\<omega> (ds1 \<union> ds2)) * card (\<omega> ds1 \<inter> ext P)"
    using \<omega>_inter propto_def sorry
  finally show ?thesis try
qed



text \<open>Bzw. die probabilisitische Relevanz von Position P für die Debatte.\<close>
theorem weak_mono_bayes:
  assumes "satisfiable ds1"
  assumes "Pr ds1 (ext P) > 0"
  assumes "Pr ds1 (\<omega> ds2) > 0"
  shows "Pr_cond ds1 (ext P) (\<omega> ds2) \<ge> Pr ds1 (ext P) \<longleftrightarrow> Pr_cond ds1 (\<omega> ds2) (ext P) \<ge> Pr ds1 (\<omega> ds2)"
proof -
have "Pr_cond ds1 (ext P) (\<omega> ds2) - Pr ds1 (ext P) = 
      Pr_cond ds1 (\<omega> ds2) (ext P) * Pr ds1 (ext P) / Pr ds1 (\<omega> ds2) - Pr ds1 (ext P)" using assms bayes by metis
  also have "... =  Pr ds1 (ext P) / Pr ds1 (\<omega> ds2) * (Pr_cond ds1 (\<omega> ds2) (ext P) - Pr ds1 (\<omega> ds2))" using assms
    by (simp add: vector_space_over_itself.scale_right_diff_distrib) 
  finally show ?thesis using assms by (simp add: Groups.mult_ac(2) Pr_cond_def inf_commute pos_le_divide_eq)
qed

theorem mono_bayes:
  assumes "satisfiable ds1"
  assumes "Pr ds1 (ext P) > 0"
  assumes "Pr ds1 (\<omega> ds2) > 0"
  shows "Pr_cond ds1 (ext P) (\<omega> ds2) > Pr ds1 (ext P) \<longleftrightarrow> Pr_cond ds1 (\<omega> ds2) (ext P) > Pr ds1 (\<omega> ds2)"
proof -
have "Pr_cond ds1 (ext P) (\<omega> ds2) - Pr ds1 (ext P) = 
      Pr_cond ds1 (\<omega> ds2) (ext P) * Pr ds1 (ext P) / Pr ds1 (\<omega> ds2) - Pr ds1 (ext P)" using assms bayes by metis
  also have "... =  Pr ds1 (ext P) / Pr ds1 (\<omega> ds2) * (Pr_cond ds1 (\<omega> ds2) (ext P) - Pr ds1 (\<omega> ds2))" using assms
    by (simp add: vector_space_over_itself.scale_right_diff_distrib) 
  finally show ?thesis using assms by (smt (verit, best) divide_le_0_iff mult_sign_intros(5) zero_less_mult_pos)
qed



text \<open>Debatte ds2 ist unabhängig von einer Debatte ds1, genau dann wenn alle Modelle von ds1 bereits ds2 erfüllen. \<close>
lemma independence:
  assumes "Pr ds1 (\<omega> ds2) > 0"
  assumes "\<forall>Q \<in> \<omega> ds1 . Q \<Turnstile> ds2"
  shows "Pr ds1 ((\<omega> ds2) \<inter> (ext P)) = Pr ds1 (\<omega> ds2) * Pr ds1 (ext P)"
proof -

  have "Pr ds1 ((\<omega> ds2) \<inter> (ext P)) - Pr ds1 (\<omega> ds2) * Pr ds1 (ext P) = 
       (1 / (card (\<omega> ds1))) * card (\<omega> ds1 \<inter> (\<omega> ds2) \<inter> (ext P)) -
       (1 / (card (\<omega> ds1))) * card (\<omega> ds1 \<inter> \<omega> ds2) * (1 / (card (\<omega> ds1))) * card (\<omega> ds1 \<inter> (ext P))" 
    using pr_card by (metis inf_assoc more_arith_simps(11))
  hence "?thesis \<longleftrightarrow> card (\<omega> ds1) * card (\<omega> ds1 \<inter> \<omega> ds2 \<inter> ext P) = card (\<omega> ds1 \<inter> \<omega> ds2) * card (\<omega> ds1 \<inter> ext P)"
    by (smt (verit) assms divide_eq_0_iff move_norm mult_cancel_right1 mult_eq_0_iff nonzero_mult_div_cancel_left of_nat_eq_iff
        of_nat_mult times_divide_eq_left times_divide_eq_right)


  moreover have "card (\<omega> ds1) * card (\<omega> ds1 \<inter> \<omega> ds2 \<inter> ext P) = card (\<omega> ds1 \<inter> \<omega> ds2) * card (\<omega> ds1 \<inter> ext P)"
  proof -
    have "\<omega> (ds1 \<union> ds2) = \<omega> ds1" using assms normal_subset_if_fullfills extended_subset by blast
    hence  "\<omega> ds1 \<inter> \<omega> ds2 = \<omega> ds1" using \<omega>_inter by simp
    thus ?thesis by simp
  qed
  ultimately show ?thesis by simp
qed

theorem extended_eq:
  assumes "satisfiable ds1"
  assumes "\<forall>Q \<in> \<omega> ds1 . Q \<Turnstile> ds2"
  shows "doj (ds1 \<union> ds2) P = doj ds1 P" 
  using extends_prob_relevency_iff independence_eq
  by (metis assms(2) doj_def equalityI extended_subset move_norm normal_subset_if_fullfills)

theorem support:
  assumes "satisfiable (ds1 \<union> ds2)"
  assumes "doj ds1 P > 0"
  shows "doj (ds1 \<union> ds2) P = doj ds1 P"
  proof -
  interpret fix_ds ds1 using assms sat_un by unfold_locales

  have "Pr ds1 (\<omega> ds2) > 0" using assms sat_un  
    by (metis Pr_cond_def Pr_to_cond div_by_0 fix_ds.intro fix_ds.pr_prob_eq measure_pmf.prob_space_axioms one_neq_zero prob_space.prob_space zero_less_measure_iff)
  hence H_gt0: "prob (\<omega> ds2) > 0" by simp
  have P_gt0: "prob (ext P) > 0" using assms(2) unfolding doj_def by simp

  (* have "Pr ds1 (ext P) > 0" using assms Pr_def f_def  *)
  have "doj (ds1 \<union> ds2) P = Pr_cond ds1 (ext P) (\<omega> ds2)" using doj_def Pr_to_cond assms sat_un by metis
  also have "... = prob_cond (ext P) (\<omega> ds2)" using Pr_cond_def by simp
  also have "... = prob_cond (\<omega> ds2) (ext P) * prob (ext P) / prob (\<omega> ds2)" using bayes H_gt0 P_gt0 by simp

  have "Pr_cond ds1 (\<omega> ds2) (ext P) = 1" using Pr_cond_def assms sat_un try

  show ?thesis sorry
  qed

(*<*)
end
(*>*)