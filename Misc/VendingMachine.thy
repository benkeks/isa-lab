theory VendingMachine
imports
  Main
begin
declare [[show_types]]


record VMSTATE =
  stock :: nat
  takings :: nat

locale VendingMachine =
fixes price :: nat
begin

definition VM_operation ::
  "VMSTATE \<Rightarrow> VMSTATE \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"
where "VM_operation vmstate vmstate' cash_tendered cash_refunded bars_delivered \<equiv>
  True" --"TODO: specify predicate"

definition exact_cash ::
  "nat \<Rightarrow> bool"
where "exact_cash cash_tendered \<equiv>
  cash_tendered = price"

definition some_stock :: "nat \<Rightarrow> bool" where "some_stock stoc = (stoc > 0)"

inductive_set state_space :: "VMSTATE set"
where 
  Init: "\<lparr> stock = 10, takings = 0 \<rparr> \<in> state_space"
    --"some initial state for the sake of a meaningful definition...."
| Step: "vmstate \<in> state_space
\<and> (\<exists> cash_tendered cash_refunded bars_delivered .
   VM_operation vmstate vmstate' cash_tendered cash_refunded bars_delivered)
\<Longrightarrow> vmstate' \<in> state_space"

end

end
