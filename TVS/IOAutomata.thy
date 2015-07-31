
theory
  IOAutomata
imports
  Main
begin

section{* Introduction *}

section{* Modelling I: The Synchronous Network Model *}

subsection{* Synchronous Network Systems *}

text {* A network basically is a directed graph without labeled edges. (p. 17) *}
locale network =
  fixes net :: "'v rel"
  assumes finNet: "finite net"
begin
  text {* Every node has a set of in-neighbors linking to it
          and out-neighbors it is linking to.*}
  definition innbrs :: "'v \<Rightarrow> 'v set"
    where "innbrs j \<equiv> {i . (i,j) \<in> net}"
  definition outnbrs :: "'v \<Rightarrow> 'v set"
    where "outnbrs i \<equiv> {j . (i,j) \<in> net}"
    
  definition nodes :: "'v set"
    where "nodes \<equiv> Domain net \<union> Range net"

  lemma finNbrs: "finite (innbrs i)" "finite (outnbrs i)"
    unfolding innbrs_def outnbrs_def
    using finNet by (induct set: finite, auto) 

  lemma finNodes: "finite nodes"
    unfolding nodes_def
    using finNet by (induct set: finite, auto)

end

definition automorphism :: "'v rel \<Rightarrow> ('v \<Rightarrow> 'v) \<Rightarrow> bool"
where "automorphism g subst \<equiv>
    bij subst \<and> (\<forall> i j . (i,j) \<in> g \<longleftrightarrow> (subst i, subst j) \<in> g)"
    (* hier bin ich mir nicht sicher, ob ich das am 1.11. richtig verstand.
       -- 2012/11/02 ben *)

subsection{* Executions *}

text {* An @{text execution} is a series of process state assignments and
        process message assignments. (p. 20)*}
record ('v, 'states, 'm) execution =
    C :: "nat \<Rightarrow> 'v \<Rightarrow> 'states"          --"process states"
    N :: "nat \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'm option"  --"messages sent"
(* actually having upper case selector functions breaks isabelle's naming conventions..
   but lower case cs and ns are quite common variable names in expressions (and it
   would be annoying to tell isabelle not to confuse a local c and a global function c...)*)

text {* With respect to some process two executions are said to be
        @{text indistinguishable} iff the process has the same sequence of states and
        incoming messages. (p. 21) *}
definition indistinguishable
    :: "'v \<Rightarrow> ('v, 'states, 'm) execution \<Rightarrow> ('v, 'states, 'm) execution \<Rightarrow> bool"
  where "indistinguishable i ex1 ex2 \<equiv>
    \<forall> r . C ex1 r i = C ex2 r i \<and> N ex1 r i = N ex2 r i"

text {* Obviously (indistinguishable i) is an equivalence relation. *}
lemma indistinguishableEquiv:
  "reflp (indistinguishable i)  \<and> symp (indistinguishable i)  \<and> transp (indistinguishable i)"
by (auto simp add: indistinguishable_def reflp_def symp_def transp_def)


subsection{* Synchronous Network Systems cont. *}

type_synonym ('von, 'states, 'm) nodeMsg   = "'states \<Rightarrow>  'von \<Rightarrow> 'm option"
type_synonym ('vin, 'states, 'm) nodeTrans = "'states \<Rightarrow> ('vin \<Rightarrow> 'm option) \<Rightarrow> 'states" 

locale ioanet =
  network net
  for   net :: "'v rel"
  +  
  fixes start :: "'v \<Rightarrow> 'states set"
    and msg   :: "'v \<Rightarrow> 'states \<Rightarrow> 'v \<Rightarrow> 'm option"
    and trans :: "'v \<Rightarrow> 'states \<Rightarrow> ('v \<Rightarrow> 'm option) \<Rightarrow> 'states"
  assumes msg_typing : "(i,j)\<notin>net \<Longrightarrow> msg i s j = None"
    --{* the lack of a channel is modelled as a permanent None-signal.
         (deviates from Lynch to avoid strange typing constructions.. )*}

begin

  definition sys_sync_ex :: "('v, 'states, 'm) execution \<Rightarrow> bool"
    where "sys_sync_ex ex \<equiv>
     (\<forall> i . C ex 0 i \<in> start i)
    \<and> (\<forall>r . \<forall> i .
          (\<forall> j . N ex (r+1) i j \<noteq> None \<longrightarrow> N ex (r+1) i j = msg i (C ex r i) j )
         \<and> C ex (r+1) i = trans i (C ex r i) (\<lambda> j . N ex (r+1) j i))"
  
   lemma sys_sync_ex_induct: "sys_sync_ex ex \<Longrightarrow> P ex 0 \<Longrightarrow>
                                (\<forall> r . P ex r \<longrightarrow> P ex (Suc r)) \<Longrightarrow> \<forall> r . P ex r"
     unfolding sys_sync_ex_def
     proof (auto)
       fix r
       assume init: "P ex 0" and
              indStep: "\<forall>r. P ex r \<longrightarrow> P ex (Suc r)" and
              defInit: "\<forall>i. C ex 0 i \<in> start i" and
              defStep: "\<forall>r i. (\<forall>j. (\<exists>y. N ex (Suc r) i j = Some y) \<longrightarrow> N ex (Suc r) i j = msg i (C ex r i) j) \<and>
              C ex (Suc r) i = trans i (C ex r i) (\<lambda>j. N ex (Suc r) j i)"
       thus "P ex r" by (induct r, auto)
    qed

  lemma sys_sync_ex_transition_induct: "sys_sync_ex ex \<Longrightarrow> P (C ex 0 i) \<Longrightarrow>
                                (\<forall> r . P (C ex r i) \<longrightarrow> P (trans i (C ex r i) (\<lambda>j. N ex (Suc r) j i)))
                                  \<Longrightarrow> \<forall> r . P (C ex r i)"
     using sys_sync_ex_induct[of ex "\<lambda> ex r. P (C ex r i)"]
     unfolding sys_sync_ex_def by (auto)

  definition M :: "('v, 'states, 'm) execution \<Rightarrow> nat \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'm option"
    where "M ex r i j \<equiv>  msg i (C ex (r - 1) i) j"
  
  definition fake_msg_loss_oracle
      :: "('v, 'states, 'm) execution \<Rightarrow> nat \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> bool"
    where "fake_msg_loss_oracle ex r i j \<equiv>
      M ex r i j \<noteq> None \<and> N ex r i j = None"

  definition ex_elects_leader :: "('states \<Rightarrow> bool) \<Rightarrow> ('v, 'states, 'm) execution \<Rightarrow> bool"
    where "ex_elects_leader isLeader ex \<equiv>
      \<exists> i r . \<forall> j s . isLeader (C ex s j) \<longleftrightarrow> (i = j \<and> s > r)"

  definition node_has_program :: "'v 
    \<Rightarrow> ('von, 'states, 'm) nodeMsg \<Rightarrow> ('vin, 'states, 'm) nodeTrans
    \<Rightarrow> ('v \<Rightarrow> 'von)                \<Rightarrow> ('v \<Rightarrow> 'vin)
    \<Rightarrow> bool"
    where "node_has_program i nMsg nTrans outMap inMap \<equiv>
      (\<forall> s .
          (\<forall> j \<in> outnbrs i . nMsg s (outMap j) = msg i s j)
       \<and>  (\<forall> j \<in> innbrs i . \<forall> asg1 asg2 . asg1 (inMap j) = asg2 j 
                  \<longrightarrow>  nTrans s asg1 = trans i s asg2))"
     
  definition identical :: "'v \<Rightarrow> 'v \<Rightarrow> bool"
    where "identical i1 i2 \<equiv>
       (\<exists> (nMsg :: (nat, 'states, 'm) nodeMsg) (nTrans::(nat, 'states, 'm) nodeTrans)
          outMap1 inMap1 outMap2 inMap2 .
           node_has_program i1 nMsg nTrans outMap1 inMap1
        \<and>  node_has_program i2 nMsg nTrans outMap2 inMap2)"

  lemma every_node_has_a_program:
      "\<exists> (nMsg :: (nat, 'states, 'm) nodeMsg) (nTrans::(nat, 'states, 'm) nodeTrans)
          outMap inMap.
           node_has_program i nMsg nTrans outMap inMap"
    unfolding node_has_program_def
    sorry
      
  lemma identity_refl : "identical i i"
    unfolding identical_def 
    using every_node_has_a_program by auto

end

section{* Leader Election in a Synchronous Ring *}

text{* bidirectional ring *}
definition ring :: "nat \<Rightarrow> nat rel"
  where "ring num \<equiv> {(i,j) . i < num \<and> j < num 
                              \<and> (   (i = (j + 1) mod num)
                                  \<or> (j = (i + 1) mod num))}"

lemma ring_size: "ring n \<subseteq> {0..n} \<times> {0..n}"
  unfolding ring_def by auto

subsection{* The Problem *}

locale leader_election_synchronous_ring =
  ioanet net
  for   net :: "nat rel"
+
  fixes num :: "nat"
  assumes ring_not_empty: "num > 0"
  assumes ring_topology: "net = ring num"
begin
  primrec ring_pred :: "nat \<Rightarrow> nat"
  where "ring_pred 0 = num - 1"
      | "ring_pred (Suc n) = n"

  lemma ring_network: "network net"
    unfolding network_def ring_topology proof-
      have "finite ({0..num} \<times> {0..num})" by auto
      thus "finite (ring num)" using ring_size[of num] by (rule rev_finite_subset)
    qed

  lemma there_are_links: "(0, num - 1) \<in> net"
    unfolding ring_topology ring_def using ring_not_empty by auto

  lemma there_are_nodes: "nodes \<noteq> {}"
    using there_are_links unfolding nodes_def by auto



subsection{* Impossibility Result for Identical Processes *}

(*all_identical: "\<forall> i j . identical i j"*)

end

subsection{* A Basic Algorithm *}

record LCR_state =
  u :: nat
  send :: "nat option"
  status :: "bool"


locale leader_election_synchronous_ring_LCR =
  leader_election_synchronous_ring start msg trans
  for start :: "nat \<Rightarrow> LCR_state set"
   and msg  :: "nat \<Rightarrow> LCR_state \<Rightarrow> nat \<Rightarrow> nat option"
   and trans :: "nat \<Rightarrow> LCR_state \<Rightarrow> (nat \<Rightarrow> nat option) \<Rightarrow> LCR_state"
+ fixes UID :: "nat \<Rightarrow> nat"
  assumes
        uniqueId: "inj UID"
    and startD: "start i = { \<lparr> u = UID i, send = Some (UID i), status = False \<rparr> }"
    and msgD:   "msg i = (\<lambda> s n .
                            if n = ((i + 1) mod num)
                              then send s
                              else None)"
    and transD: "trans i = (\<lambda> s asg.
                             case (asg (ring_pred i)) of
                                None   \<Rightarrow> 
                                      s \<lparr> send := None \<rparr>
                             |  Some v \<Rightarrow>
                                  if v > u s then
                                      s \<lparr> send := Some v \<rparr> 
                                  else if v = u s then
                                      s \<lparr> send := None,
                                          status := True \<rparr>
                                  else
                                      s \<lparr> send := None \<rparr>)"
begin

lemma u_constant: "sys_sync_ex ex \<Longrightarrow> \<forall> r. u (C ex r i) = UID i"
  proof (rule sys_sync_ex_transition_induct[of ex "\<lambda> s . u s = UID i" i],
          simp, simp add: sys_sync_ex_def startD, clarify)
    fix r
    assume IV: "u (C ex r i) = UID i"
    have "\<And> x someAsg. u x = u (trans i x someAsg)" proof-
      fix x someAsg
      show "u x = u (trans i x someAsg)" 
        unfolding transD
        by (cases "someAsg (ring_pred i) = None", auto)
    qed
    from this[of "C ex r i"] IV
      show "u (trans i (C ex r i) (\<lambda>j. N ex (Suc r) j i)) = UID i " by auto
  qed

definition uids :: "nat set"
  where "uids \<equiv> UID ` nodes"

lemma uids: "finite uids" "uids \<noteq> {}"
  unfolding uids_def using finNodes there_are_nodes by auto

definition u_max :: "nat"
  where "u_max \<equiv> Max uids"

lemma u_max: "u2 \<in> uids \<Longrightarrow> u2 \<le> u_max"
 unfolding u_max_def using uids by (auto)

definition i_max :: "nat"
  where "i_max \<equiv> THE i . i \<in> nodes \<and> UID i = u_max"
      
end

end


