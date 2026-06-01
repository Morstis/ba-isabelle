theory wtDS
  imports Main  "HOL.Rat" defDS theoremsDS
begin






(* Hier habe ich versucht die Theorie aus dem alten Paper von Betz 2006
zu formalisieren: 
*)

(*
Der Grundraum kann nicht eine koherente Position sein.  
*)
definition \<Omega>_fail :: "ds \<Rightarrow> position set" where
  "\<Omega>_fail ds = {p. coherent p ds \<and> domain_ds ds = image sen p}"

lemma omega_fail:
  assumes "\<omega> \<in> \<Omega>_fail ds"
  shows "doj \<omega> ds \<noteq> 1"
proof -
  have "{p. \<omega> \<subseteq> p \<and> p \<Turnstile> ds} = {p. {} \<subseteq> p \<and> p \<Turnstile> ds}"
    nitpick
    oops


(* Proposition 6 (Degrees of justification are probabilities)
   Degrees of justification satisfy the Kolmogorov axioms.

   Proof: Let \<tau> = \<langle>T, A, U\<rangle> be a dialectical structure. 
   We have to show:

   (1) 0 \<le> DoJ_\<tau>(P) \<le> 1          for every position P
   (2) DoJ_\<tau>(\<Omega>) = 1               for every \<tau>-certain position \<Omega>
   (3) DoJ_\<tau>(P1 \<or> P2) = DoJ_\<tau>(P1) + DoJ_\<tau>(P2) 
                                   for two \<tau>-exclusive positions P1 and P2
  
   Definition 9 (\<tau>-exclusive partial positions)
   Let \<tau> = \<langle>T, A, U\<rangle> be a dialectical structure.
   Two partial positions P1 and P2 are called "\<tau>-exclusive" if and only if
   there is no coherent and complete position on \<tau> which extends both P1 and P2.

   Aus Betz: On Degrees of Justification

*)


(* Wenn P eine Teilmenge von allen koherenten Positionen auf ds ist, nennen wir P tau_certain *)
definition tau_certain :: "position \<Rightarrow> ds \<Rightarrow> bool"
  where "tau_certain P ds = (\<forall>V. (V \<Turnstile> ds \<longrightarrow> P \<subseteq> V))"

(* P und Q sind tau_exclusive, wenn es keine koherente Position gibt, die sowohl P als auch Q erweitert.  *)
definition tau_exclusive :: "position \<Rightarrow> position \<Rightarrow> ds \<Rightarrow> bool"
  where "tau_exclusive P Q ds = (\<forall>V. (V \<Turnstile> ds \<longrightarrow> \<not>(P \<subseteq> V \<and> Q \<subseteq> V)))"

(* tau_certain Positionen bilden eventuell den Grundraum *)
definition \<Omega> :: "ds \<Rightarrow> position set" where
"\<Omega> ds =  {p. tau_certain p ds}"

(* Die Wahrscheinlichkeit aller Ereignisse ist 1 *)
lemma omega:
  assumes "\<omega> \<in> \<Omega> ds"
  assumes sat: "\<sigma> {} ds > 0"
  shows "doj \<omega> ds = 1"
proof -
  have "{p. (\<omega> \<union> {}) \<subseteq> p \<and> p \<Turnstile> ds} = {p. {} \<subseteq> p \<and> p \<Turnstile> ds}"
    using \<Omega>_def assms tau_certain_def by auto
  hence "\<sigma> (\<omega> \<union> {}) ds = \<sigma> {} ds" using mods_def \<sigma>_def by presburger 
  thus ?thesis using sat unfolding doj_cond_def
    by (simp add: doj_cond_def doj_def)
qed

(* doj ist eine Funktion von der Potenzmenge des Grundraums auf [0, 1] *)
lemma omaga_between0_1:
  assumes "\<omega> \<in> \<Omega> ds"
  assumes sat: "\<sigma> {} ds > 0"
  shows "\<forall>P \<subseteq> \<omega> . 0 \<le> doj P ds \<and> doj P ds \<le> 1 "
proof -
  show ?thesis using between0_1 by presburger
qed

(* es existiert eine Abzählbare Untermenge von jeden \<omega>, die Wahrscheinlichkeit 1 hat. *)
lemma omega_0:
  assumes "\<sigma> {} ds > 0"
  assumes "\<omega> \<in> \<Omega> ds"

  shows "\<exists>x \<subseteq> \<omega>. doj x ds = 1"
proof -
  show ?thesis using doj_cond_def unfolding doj_cond_def 
    by (meson assms(1,2) omega order_refl)
qed

(* Sigma Additivität: Der Begründungsgrad von zwei tau_exclusive Positionen ist 
die Summe der einzelnen Begründungsgrade. 
*)

lemma sigma_simple:
  assumes "\<omega> \<in> \<Omega> ds"
  assumes "tau_exclusive P Q ds"
  shows "doj (P \<union> Q) ds = doj P ds + doj Q ds"
proof -
  have only_sigma_relevant:  "(\<Sum>l \<in> P . doj {l} ds) = (\<Sum>l \<in> P . rat_of_nat (\<sigma> {l} ds)) / rat_of_nat (\<sigma> {} ds)"
    by (metis (mono_tags, lifting) doj_cond_def doj_def insert_is_Un sum.cong
          sum_divide_distrib)

  have "\<sigma> (P \<union> Q) ds = \<sigma> P ds + \<sigma> Q ds" 
  proof (rule order_antisym)
    show "\<sigma> (P \<union> Q) ds \<le> \<sigma> P ds + \<sigma> Q ds"
      by (smt (verit, del_insts) Collect_empty_eq \<sigma>_def
          assms(2) card_mono empty_iff fin_mods le_sup_iff
          mods_def subsetI tau_exclusive_def
          trans_le_add2)
  next
    show "\<sigma> (P \<union> Q) ds \<ge> \<sigma> P ds + \<sigma> Q ds" sorry
  qed
  thus ?thesis using only_sigma_relevant
    by (simp add: add_divide_distrib doj_cond_def doj_def) 
  qed


(* Ende der Theorie aus dem Paper von Betz. 
  Ich denke die funkioniert, ist jedoch ziemlich eingeschränkt.
  Im Folgenden habe ich versucht, die Überlegungen von 13.05. zu formalisieren. 
  Das sind eher Skizzen.
*)


(*
Die Summe der dojs einzelner Literale einer konsistenten Position
ist nicht zwingend kleiner-gleich 1.  

Gegenbeispiel:
Sei ds = {({}, a), ({}, b)}. 
Dann \<sigma> ds = 1,
und  \<sigma> {} ds = 1

Aber \<sigma> {a} ds = 1
und  \<sigma> {b} ds = 1

Dann also:
doj {a} ds + doj {b} ds = (\<sigma> {a} ds + \<sigma> {b} ds) / \<sigma> {} ds = 2 = 1 !?

*)
lemma
  assumes "P \<noteq> {}"
  assumes "consistent P ds"
  shows "(\<Sum>l \<in> P . doj {l} ds) \<le> 1"
proof - 
  show ?thesis nitpick [user_axioms = true]
    oops

(*
Das dieses Theorem nicht stimmen kann folgt direkt aus der Falschheit des vorherigen Lemmas:
Wähle P = {a, b}. ds = {({}, a), ({}, b)}, dann ist sie summe wieder 2,
aber doj ^P ds muss kleiner als 1 sein.
*)
theorem gte_sum:
  assumes "P \<noteq> {}"
  shows "doj P ds \<ge> (\<Sum>l \<in> P . doj {l} ds)"
proof - 

  oops

(*
DoJ ist unter der naiven Vereinigung nicht abgeschlossen:
Wähle P, sodass doj P ds > 0, Q = {}, dann
doj (P \<union> Q) ds = 0 < doj P ds \<le> 1.
Aber doj Q ds = doj {} ds = 1
Daher: doj P ds + doj Q ds > 1 \<and> 0 \<le> doj ^P ^ds \<le> 1 \<Longrightarrow> False 

Selbst wenn beide Positionen Aussagen treffen,
findet nitpick ein Gegenbeispiel
*)
theorem doj_union_closed:
  assumes "P \<noteq> {} \<and> Q \<noteq> {}"
  assumes "image sen P \<inter> image sen Q = {}"
  shows  "doj (P \<union> Q) ds = doj P ds + doj Q ds"
  
proof -
  show ?thesis nitpick
    oops



(* Unter der Vereinigung generell nicht abgeschlossen. Nitick findet gute gegenbeispiele*)

(* nicht wahr für allgm Positionen *)
lemma union_mods_wrong: "\<forall>P Q. \<exists>C. mods P ds \<union> mods Q ds = mods C ds" nitpick oops

(* nicht wahr für Positionen, deren Schnitt leer ist *)
lemma union_mods_wrong: "\<forall>P Q. \<exists>C. (P \<inter> Q = {}) \<longrightarrow>  mods P ds \<union> mods Q ds = mods C ds" nitpick oops

(* nicht wahr für Positionen, die über unterschiedliche Sätze Aussagen treffen *)
lemma union_mods_wrong: "\<forall>P Q. \<exists>C. (image sen P \<inter> image sen Q = {}) \<longrightarrow>  mods P ds \<union> mods Q ds = mods C ds" nitpick oops



(* 
Hier der Versuche das zu beweisen... 
Sei P = {Pos a}, Q = {Pos b}, dann:
mods P {} \<union> mods Q {} = a \<or> b
a b       \<union>   a b   =   a b
1 0           0 1       0 1
1 1           1 1       1 0
                        1 1

Aber dann müssten wir ein C finden, sodass C |= Pos a \<or> Pos b. 
Aber C = \<And>l :: literal \<noteq> Pos a \<or> Pos b
*)
lemma union_mods:
  assumes "\<sigma> {} ds > 0"
  shows "\<not>(\<forall>P Q. \<exists>C. mods P {} \<union> mods Q {} = mods C {})"
proof
  fix a b 
  have negSub: "\<forall>V . V \<Turnstile> {} \<and> (Pos a \<in> V \<or> Pos b \<in> V) \<longrightarrow> \<not>({Neg a, Neg b} \<subseteq> V)" 
    using coherent_def complete_consistent_def consistent_def by auto
  assume "\<forall>P Q. \<exists>C. mods P {} \<union> mods Q {} = mods C {}"
  then obtain C where "mods {Pos a} {} \<union> mods {Pos b} {} = mods C {}"
    by blast

  have "{Pos a, Neg b} \<in> mods {Pos a} {} \<union> mods {Pos b} {}" and
    "{Neg a, Pos b} \<in> mods {Pos a} {} \<union> mods {Pos b} {}"  sorry 
  hence "{Pos a, Neg b} \<in> mods C {} \<and> {Neg a, Pos b} \<in> mods C {}"
    using \<open>mods {Pos a} {} \<union> mods {Pos b} {} = mods C {}\<close> by blast 
 

  have "{V. C \<subseteq> V \<and> V \<Turnstile> {}} = {V. (Pos a \<in> V \<or> Pos b \<in> V) \<and> V \<Turnstile> {}}"
    unfolding coherent_extensions_def
    by (metis (lifting) UnCI UnE \<open>mods {Pos a} {} \<union> mods {Pos b} {} = mods C {}\<close> bot_least
        mods_def insert_subset mem_Collect_eq) 
  then obtain V where "V \<Turnstile> {} \<and> (C \<subseteq> V \<longleftrightarrow> (Pos a \<in> V \<or> Pos b \<in> V))" 
    by (metis (no_types, lifting) coherent_def complete_consistent_def complete_def
        consistent_def empty_iff literal.disc(1,2) literal.sel(1) mem_Collect_eq)
  thus "False" unfolding coherent_def
    oops


end