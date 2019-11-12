(* Yihao Sun "ysun67@syr.edu"
   2019 in Syracuse

   this is counter plugin to count how many "JMP" expr in deasmed
   IR *)

open Core_kernel
open Bap.Std
open Format

include Self()

(** try to directly visit IL 
    disasm can turn a program into BIL(in a lazy sequence)*)
let countp proj =
  let instructions = Disasm.insns (Project.disasm proj) in
  (* where a instr is jump to *)
  let is_jump men_i_tuple =
    match men_i_tuple with
    (* using modal properties of Ins *)
    | (mem, i) ->
      if Insn.is Insn.jump i
      then (printf "hit jump instr %a \n" Insn.pp_adt i;
            true)
      else false in
  let count_jmp ins = Seq.count ins is_jump in
  count_jmp instructions

let pp_addr ppf a =
  Addr.pp_generic ~prefix:`none ~case:`lower ppf a

let print_fun_reg proj =
  let pp_bil ppf = Bil.Io.print ppf in
  let instructions = Disasm.insns (Project.disasm proj) in
  let pfun men_i_tuple =
    match men_i_tuple with
    | (mem, i) ->
      let addr = Memory.min_addr mem in
      if Insn.is Insn.call i
      then printf "%a: %s@\n%a@\n" pp_addr addr (Insn.asm i) pp_bil (Insn.bil i)
  in
  Seq.iter instructions pfun 


let main proj =
  print_fun_reg proj
  (* let term_num = countp proj in
  printf "there are %d terms in program" term_num *)

let () = Project.register_pass' main
