theory Reverse
imports "~/verification/mainline/l4v/tools/autocorres/AutoCorres"
begin

install_C_file "reverse.c"
autocorres "reverse.c"

locale ref =
  fixes
    get :: "'ref \<Rightarrow> 'state \<Rightarrow> 'val" and
    set :: "'ref \<Rightarrow> 'val \<Rightarrow> 'state \<Rightarrow> 'state" and
    ok  :: "'ref \<Rightarrow> 'state \<Rightarrow> bool"
  assumes
    ok_pres [simp]: "\<And> p q r s. ok p s \<Longrightarrow> ok p (set q r s)" and
    set_dup [simp]: "\<And> p v w s. ok p s \<Longrightarrow> set p v (set p w s) = set p v s" and
    get_set [simp]: "\<And> p v s. ok p s \<Longrightarrow> get p (set p v s) = v" and
    set_get [simp]: "\<And> p s. ok p s \<Longrightarrow> set p (get p s) s = s" and
    get_com: "\<And> p q v s. ok p s \<Longrightarrow> ok p s \<Longrightarrow> p \<noteq> q \<Longrightarrow> get p (set q v s) = get p s" and
    set_com: "\<And> p q v w s. ok p s \<Longrightarrow> ok q s \<Longrightarrow> p \<noteq> q \<Longrightarrow> set p v (set q w s) = set q w (set p v s)"

locale ptr_chain = ref get_next set_next ok
  for
    get_next :: "'ptr \<Rightarrow> 'state \<Rightarrow> 'ptr" and
    set_next :: "'ptr \<Rightarrow> 'ptr \<Rightarrow> 'state \<Rightarrow> 'state" and
    ok :: "'ptr \<Rightarrow> 'state \<Rightarrow> bool" +
  fixes
    null :: "'ptr"
  assumes
    ok_not_null [simp]: "\<not> ok null s"

context ptr_chain begin

primrec list_eq :: "'state \<Rightarrow> 'ptr \<Rightarrow> 'ptr list \<Rightarrow> bool" where
  "list_eq s p [] = (p = null)" |
  "list_eq s p (q # r) = (ok p s \<and> p = q \<and> list_eq s (get_next p s) r)"

primrec list_rev :: "'ptr \<Rightarrow> 'ptr list \<Rightarrow> 'state \<Rightarrow> 'state" where
  "list_rev e (p # ps) = list_rev p ps \<circ> set_next p e" |
  "list_rev e [] = id"

primrec rev_invariant :: "'state \<Rightarrow> 'ptr list \<Rightarrow> 'ptr \<times> 'ptr \<Rightarrow> 'state \<Rightarrow> bool" where
  "rev_invariant i ps (p,r) s =
    (\<exists> ps' rs.
      distinct ps \<and>
      ps = rev rs @ ps' \<and>
      s = list_rev null (rev rs) i \<and>
      list_eq s p ps' \<and>
      list_eq s r rs)"

fun rev_measure :: "('ptr \<times> 'ptr) \<times> 'state \<Rightarrow> nat" where
  "rev_measure ((p,r),s) = length (The (list_eq s p))"

lemma list_eq_unique: "list_eq s p ps \<Longrightarrow> list_eq s p qs \<Longrightarrow> ps = qs"
  by (induction ps arbitrary: p qs; case_tac qs; fastforce)

lemma list_get_eq [simp]: "list_eq s p ps \<Longrightarrow> The (list_eq s p) = ps"
  using list_eq_unique by blast

lemma list_eq_null [dest]: "list_eq s null ps \<Longrightarrow> ps = []"
  by (cases ps) auto

lemma list_eq_not_null_valid: "p \<noteq> null \<Longrightarrow> list_eq s p ps \<Longrightarrow> ok p s"
  by (cases ps) auto

lemma list_eq_up: "ok q s \<Longrightarrow> q \<notin> set ps \<Longrightarrow> list_eq s p ps \<Longrightarrow> list_eq (set_next q r s) p ps"
  by (induction ps arbitrary: p) (auto simp: get_com)

lemma list_eq_app: "list_eq s p (ps @ q # qs) \<Longrightarrow> list_eq s q (q # qs)"
  by (induction ps arbitrary: p) auto

lemma list_eq_distinct: "list_eq s p ps \<Longrightarrow> distinct ps"
  proof (induction ps arbitrary: s p)
    case (Cons p' ps)
    hence Cons':
      "list_eq s p (p # ps)"
      "distinct ps"
      "p' = p"
      "ok p s"
      by auto
    {
      assume P: "p \<in> set ps"
      obtain h t where S: "ps = h @ p # t" using split_list[OF P] by blast
      hence T: "list_eq s p (p # t)" using Cons' list_eq_app by simp
      have False using list_eq_unique[OF Cons'(1) T] S by simp
    }
    thus ?case using Cons' by auto
  qed auto

lemma list_eq_next:
  "p \<noteq> null \<Longrightarrow> ps = p' # ps' \<Longrightarrow> list_eq s p ps \<Longrightarrow> list_eq (set_next p q s) (get_next p s) ps'"
  by (frule list_eq_distinct, cases ps) (auto simp: list_eq_up)

lemma list_rev_app: "list_rev e (ps @ q # qs) = list_rev q qs \<circ> list_rev e (ps @ [q])"
  by (induction ps arbitrary: e) auto

lemma list_rev_snoc:
  "list_eq s' r rs \<Longrightarrow> set_next p r (list_rev null (rev rs) s) = list_rev null (rev rs @ [p]) s"
  by (cases rs; clarsimp simp: list_rev_app[where qs="[p]"])

end

context reverse begin

definition get_next_node :: "node_C ptr \<Rightarrow> lifted_globals \<Rightarrow> node_C ptr" where
  "get_next_node p s \<equiv> next_C (heap_node_C s p)"

definition set_next_node :: "node_C ptr \<Rightarrow> node_C ptr \<Rightarrow> lifted_globals \<Rightarrow> lifted_globals" where
  "set_next_node p q \<equiv> heap_node_C_update (\<lambda>h. h (p := next_C_update (\<lambda>_. q) (h p)))"

abbreviation ok_node_ptr :: "node_C ptr \<Rightarrow> lifted_globals \<Rightarrow> bool" where
  "ok_node_ptr p s \<equiv> p \<noteq> NULL \<and> is_valid_node_C s p"

sublocale node_ptr_chain?: ptr_chain get_next_node set_next_node ok_node_ptr NULL
  unfolding get_next_node_def[abs_def] set_next_node_def[abs_def]
  by unfold_locales (auto simp: fun_upd_twist fun_upd_other fun_upd_same)

lemma reverse'_correct:
  "\<lbrace> \<lambda> s. s = i \<and> list_eq s p ps \<rbrace>
    reverse' p
   \<lbrace> \<lambda> r s. s = list_rev NULL ps i \<and> list_eq s r (rev ps) \<rbrace>!"
  unfolding
    reverse'_def
    get_next_node_def[symmetric] set_next_node_def[symmetric]
    whileLoop_add_inv[where I="rev_invariant i ps" and M="rev_measure"]
  apply (wp; clarsimp)
  subgoal for p r ps' rs
   apply (cases ps'; clarsimp simp: list_get_eq[OF list_eq_next[where ps=ps']])
   subgoal for ps''
    apply (rule exI[where x=ps''])
    apply (rule exI[where x="p # rs"])
    apply (auto simp: list_eq_next list_eq_up)
    by (simp add: list_rev_snoc)
   done
  subgoal by auto
  subgoal by (intro conjI exI) (auto simp: list_eq_distinct)
  done

lemma reverse_simpl_correct:
  assumes
    "\<And> s. lift_global_heap (globals s) = i \<and> list_eq (lift_global_heap (globals s)) p ps \<Longrightarrow> list_' s = p"
  shows
    "\<Gamma>, \<Theta> \<turnstile>\<^sub>t\<^bsub>/F\<^esub>
       {s. lift_global_heap (globals s) = i \<and> list_eq (lift_global_heap (globals s)) p ps}
         Call reverse_'proc
       {s. lift_global_heap (globals s) = list_rev NULL ps i \<and> list_eq (lift_global_heap (globals s)) (ret__ptr_to_struct_node_C_' s) (rev ps)}, E"
  apply (rule hoaret_from_ac_corres[OF reverse'_ac_corres validE_NF_liftE[OF reverse'_correct], simplified])
  by (metis (full_types) assms myvars.simps(4) state.simps(1))

end

end
