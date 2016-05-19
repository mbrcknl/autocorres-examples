theory GraphMark
imports "~/verification/mainline/l4v/tools/autocorres/AutoCorres"
begin

install_C_file "graph_mark.c"
autocorres [heap_abs_syntax] "graph_mark.c"

context graph_mark begin

type_synonym mark = "32 word"
type_synonym state_pred = "lifted_globals \<Rightarrow> bool"

definition out :: "lifted_globals \<Rightarrow> node_C ptr \<Rightarrow> node_C ptr set" where
  "out s p \<equiv> { s[p]\<rightarrow>left, s[p]\<rightarrow>right }"

inductive_set reach :: "lifted_globals \<Rightarrow> node_C ptr set \<Rightarrow> node_C ptr set"
  for s :: lifted_globals and R :: "node_C ptr set"
  where
    reach_root: "p \<noteq> NULL \<Longrightarrow> p \<in> R \<Longrightarrow> p \<in> reach s R"
  | reach_step: "q \<noteq> NULL \<Longrightarrow> q \<in> out s p \<Longrightarrow> p \<in> reach s R \<Longrightarrow> q \<in> reach s R"

definition mark :: "bool \<Rightarrow> node_C \<Rightarrow> node_C" where
  "mark c node \<equiv> if c then node \<lparr> mark_C := 3 \<rparr> else node"

definition mark_set :: "node_C ptr set \<Rightarrow> lifted_globals \<Rightarrow> lifted_globals" where
  "mark_set R s \<equiv> heap_node_C_update (\<lambda> h p. mark (p \<in> R) (h p)) s"

definition mark_precondition :: "state_pred \<Rightarrow> node_C ptr \<Rightarrow> state_pred" where
  "mark_precondition P root \<equiv> \<lambda> s. let R = reach s {root} in
    (\<forall> p \<in> R. is_valid_node_C s p \<and> s[p]\<rightarrow>mark = 0) \<and> P (mark_set R s)"

type_synonym path_upd_t =
  "lifted_globals \<Rightarrow> node_C ptr set
    \<Rightarrow> node_C ptr \<Rightarrow> node_C ptr \<Rightarrow> node_C ptr \<Rightarrow> node_C ptr list \<Rightarrow> lifted_globals option"

primrec tail_upd :: path_upd_t where
  "tail_upd s M r q p [] = (if p = NULL \<and> q = r then Some s else None)" |
  "tail_upd s M r q p (p' # ps) =
   (if p \<noteq> p' then None
    else if s[p]\<rightarrow>mark = 1 then
      tail_upd s[p\<rightarrow>left := q][p\<rightarrow>right := s[p]\<rightarrow>left] M r p s[p]\<rightarrow>right ps
    else if s[p]\<rightarrow>mark = 2 \<and> s[p]\<rightarrow>right \<in> M then
      tail_upd s[p\<rightarrow>right := q][p\<rightarrow>left := s[p]\<rightarrow>right] M r p s[p]\<rightarrow>left ps
    else None)"

primrec path_upd :: path_upd_t where
  "path_upd s M r q p [] = (if p = NULL \<and> q = r \<and> (r = NULL \<or> r \<in> M) then Some s else None)" |
  "path_upd s M r q p (p' # ps) =
   (if p \<noteq> p' then None
    else if s[p]\<rightarrow>mark = 0 then
      tail_upd s M r p q ps
    else if s[p]\<rightarrow>mark = 1 \<and> q \<in> M then
      tail_upd s[p\<rightarrow>left := q][p\<rightarrow>right := s[p]\<rightarrow>left] M r p s[p]\<rightarrow>right ps
    else if s[p]\<rightarrow>mark = 2 \<and> s[p]\<rightarrow>right \<in> M \<and> q \<in> M then
      tail_upd s[p\<rightarrow>right := q][p\<rightarrow>left := s[p]\<rightarrow>right] M r p s[p]\<rightarrow>left ps
    else None)"

primrec mark_invariant :: "state_pred \<Rightarrow> node_C ptr \<Rightarrow> node_C ptr \<times> node_C ptr \<Rightarrow> state_pred" where
  "mark_invariant P root (p,q) s =
    (\<exists> t u path M.
      let
        R = reach t {root};
        U = R - M;
        F = U - set path
      in
        P t \<and>
        set path \<subseteq> R \<and>
        M \<subseteq> R \<and>
        reach s {p,q} = R \<and>
        reach t M = M \<and>
        path_upd s M root q p path = Some u \<and>
        mark_set U u = t \<and>
        (\<forall> p \<in> R. is_valid_node_C s p) \<and>
        (\<forall> p \<in> M. s[p]\<rightarrow>mark = 3) \<and>
        (\<forall> p \<in> F. s[p]\<rightarrow>mark = 0))"

fun mark_measure :: "(node_C ptr \<times> node_C ptr) \<times> lifted_globals \<Rightarrow> nat" where
  "mark_measure ((p,q),s) = setsum (\<lambda> p. 3 - unat s[p]\<rightarrow>mark) (reach s {p,q})"

definition mark_incr :: "node_C ptr \<Rightarrow> lifted_globals \<Rightarrow> lifted_globals" where
  "mark_incr p \<equiv> heap_node_C_update (\<lambda> h. h(p := mark_C_update (\<lambda> m. m + 1) (h p)))"

lemma mark_incr_mark [simp]: "(mark_incr p s)[p]\<rightarrow>mark = s[p]\<rightarrow>mark + 1"
  unfolding mark_incr_def by (simp add: fun_upd_def graph_mark.get_node_mark_def)

lemma mark_incr_left [simp]: "(mark_incr q s)[p]\<rightarrow>left = s[p]\<rightarrow>left"
  unfolding mark_incr_def by (simp add: fun_upd_def graph_mark.get_node_left_def)

lemma mark_incr_right [simp]: "(mark_incr q s)[p]\<rightarrow>right = s[p]\<rightarrow>right"
  unfolding mark_incr_def by (simp add: fun_upd_def graph_mark.get_node_right_def)

lemma out_mark_incr [simp]: "out (mark_incr q s) = out s"
  unfolding out_def[abs_def] by fastforce

lemma mark_set_left [simp]: "(mark_set R s)[p]\<rightarrow>left = s[p]\<rightarrow>left"
  unfolding mark_set_def mark_def by (simp add: graph_mark.get_node_left_def)

lemma mark_set_right [simp]: "(mark_set R s)[p]\<rightarrow>right = s[p]\<rightarrow>right"
  unfolding mark_set_def mark_def by (simp add: graph_mark.get_node_right_def)

lemma out_mark_set [simp]: "out (mark_set R s) = out s"
  unfolding out_def[abs_def] by fastforce

lemma mark_incr_node_valid [simp]: "is_valid_node_C (mark_incr q s) p = is_valid_node_C s p"
  unfolding mark_incr_def by simp

lemma mark_incr_left_upd [simp]:"(mark_incr q s)[p\<rightarrow>left := v] = mark_incr q s[p\<rightarrow>left := v]"
  unfolding mark_incr_def
  by (smt fun_upd_def fun_upd_twist fun_upd_upd graph_mark.update_node_left_def
          lifted_globals.surjective lifted_globals.update_convs(5) node_C_updupd_diff(2))

lemma mark_incr_right_upd [simp]:"(mark_incr q s)[p\<rightarrow>right := v] = mark_incr q s[p\<rightarrow>right := v]"
  unfolding mark_incr_def
  by (smt fun_upd_def fun_upd_twist fun_upd_upd graph_mark.update_node_right_def
          lifted_globals.surjective lifted_globals.update_convs(5) node_C_updupd_diff(1))

lemma null_path_empty [dest]:
  assumes
    "path_upd s M root q NULL path = Some u"
    "set path \<subseteq> reach t roots"
  shows
    "path = []"
  using assms by (cases path; auto elim: reach.cases)

lemma reachable_subset: assumes "R \<subseteq> S" shows "reach s R \<subseteq> reach s S"
  proof -
    { fix p have "p \<in> reach s R \<Longrightarrow> R \<subseteq> S \<Longrightarrow> p \<in> reach s S"
      by (induction rule: reach.induct) (auto intro: reach.intros) }
    thus ?thesis using assms by auto
  qed

lemma reachable_with_null: "reach s R = S \<Longrightarrow> R' = insert NULL R \<Longrightarrow> reach s R' = S"
  sorry

lemma reachable_null [simp]: "reach s {NULL} = {}"
  proof -
    { fix p have "p \<in> reach s {NULL} \<Longrightarrow> False" by (induction rule: reach.induct) auto }
    thus ?thesis by auto
  qed

lemma reachable_empty [simp]: "reach s {} = {}"
  by (metis empty_subsetI graph_mark.reachable_subset reachable_null subset_antisym)

lemma mark_set_empty [simp]: "mark_set {} u = u"
  unfolding mark_set_def mark_def by simp

lemma graph_mark'_correct: "\<lbrace> mark_precondition P root \<rbrace> graph_mark' root \<lbrace> \<lambda> _. P \<rbrace>!"
  unfolding
    graph_mark'_def mark_precondition_def
    whileLoop_add_inv[where I="mark_invariant P root" and M="mark_measure"]
    mark_incr_def[symmetric]
  apply (wp; clarsimp)
  subgoal for p q s t u path M
   sorry
  subgoal for q s t u path M
   apply (clarsimp simp: Let_def)
   apply (frule (1) null_path_empty)
   apply (clarsimp split: split_if_asm)
   apply (cases "root = NULL"; clarsimp)
   apply (frule reachable_subset[of "{root}" M t, simplified])
   by auto
  subgoal for s
   apply (rule exI[where x="mark_set (reach s {root}) s"])
   apply (rule exI[where x=s])
   apply (rule exI[where x="if root = NULL then [] else [root]"])
   apply (rule exI[where x="{}"])
   apply (cases "root = NULL"; clarsimp simp: Let_def)
   sorry
  done

end

end
