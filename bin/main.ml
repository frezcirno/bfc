type instruction =
  | Advance of int
  | Back of int
  | Add of int
  | Sub of int
  | Output
  | Input
  | Loop of instruction list

let int_to_bytes n len =
  let rec aux acc n =
    if List.length acc >= len then acc else aux ((n land 0xFF) :: acc) (n lsr 8)
  in
  aux [] n |> List.rev

let merge_consecutive instructions =
  let rec merge acc = function
    | [] -> List.rev acc
    | Advance n :: Advance m :: rest -> merge acc (Advance (n + m) :: rest)
    | Back n :: Back m :: rest -> merge acc (Back (n + m) :: rest)
    | Add n :: Add m :: rest -> merge acc (Add (n + m) :: rest)
    | Sub n :: Sub m :: rest -> merge acc (Sub (n + m) :: rest)
    | Loop sub :: rest -> merge (Loop (merge [] sub) :: acc) rest
    | hd :: rest -> merge (hd :: acc) rest
  in
  merge [] instructions

let parse code =
  let rec parse' acc = function
    | [] -> (List.rev acc, [])
    | '>' :: rest -> parse' (Advance 1 :: acc) rest
    | '<' :: rest -> parse' (Back 1 :: acc) rest
    | '+' :: rest -> parse' (Add 1 :: acc) rest
    | '-' :: rest -> parse' (Sub 1 :: acc) rest
    | '.' :: rest -> parse' (Output :: acc) rest
    | ',' :: rest -> parse' (Input :: acc) rest
    | '[' :: rest ->
        let subacc, rest = parse' [] rest in
        parse' (Loop subacc :: acc) rest
    | ']' :: rest -> (List.rev acc, rest)
    | _ :: rest -> parse' acc rest
  in
  parse' [] code |> fst

let interpret instructions =
  let rec interpret' instructions memory dp =
    match instructions with
    | [] -> memory
    | Advance n :: rest -> interpret' rest memory (dp + n)
    | Back n :: rest -> interpret' rest memory (dp - n)
    | Add n :: rest ->
        memory.(dp) <- memory.(dp) + n;
        interpret' rest memory dp
    | Sub n :: rest ->
        memory.(dp) <- memory.(dp) - n;
        interpret' rest memory dp
    | Output :: rest ->
        print_char (Char.chr memory.(dp));
        interpret' rest memory dp
    | Input :: rest ->
        let c = String.get (read_line ()) 0 |> Char.code in
        memory.(dp) <- c;
        interpret' rest memory dp
    | Loop loop :: rest ->
        if memory.(dp) = 0 then interpret' rest memory dp
        else interpret' (loop @ instructions) memory dp
  in
  interpret' instructions (Array.make 30000 0) 0

let dump instructions =
  let rec dump' indents = function
    | [] -> ()
    | instr :: rest ->
        Printf.printf "%s" (String.make (2 * indents) ' ');
        (match instr with
        | Advance n -> Printf.printf "%s" (String.make n '>')
        | Back n -> Printf.printf "%s" (String.make n '<')
        | Add n -> Printf.printf "%s" (String.make n '+')
        | Sub n -> Printf.printf "%s" (String.make n '-')
        | Output -> Printf.printf "."
        | Input -> Printf.printf ","
        | Loop sub ->
            Printf.printf "[\n";
            dump' (indents + 1) sub;
            Printf.printf "%s]\n" (String.make (2 * indents) ' '));
        Printf.printf "\n";
        dump' indents rest
  in
  dump' 0 instructions

let compile instructions =
  let rec compile' instructions acc =
    match instructions with
    | [] -> acc
    | Advance n :: rest ->
        compile' rest (acc @ (* addq  $n, %rdi *) [ 0x48; 0x83; 0xc7; n ])
    | Back n :: rest ->
        compile' rest (acc @ (* subq  $n, %rdi *) [ 0x48; 0x83; 0xef; n ])
    | Add n :: rest ->
        compile' rest (acc @ (* addb  $n, (%rdi) *) [ 0x80; 0x07; n ])
    | Sub n :: rest ->
        compile' rest (acc @ (* subb  $n, (%rdi) *) [ 0x80; 0x2f; n ])
    | Output :: rest ->
        compile' rest
          (acc
           (*
          pushq   %rdi
          pushq   %rsi
          pushq   %rdx
          pushq   %rax
          *)
         @ [ 0x57; 0x56; 0x52; 0x50 ]
          (*
          movl    $1, %eax
          movq    %rdi, %rsi
          movl    $1, %edi
          movl    $1, %edx
          syscall
          *)
          @ [ 0xb8; 0x01; 0x00; 0x00; 0x00 ]
          @ [ 0x48; 0x89; 0xfe ]
          @ [ 0xbf; 0x01; 0x00; 0x00; 0x00 ]
          @ [ 0xba; 0x01; 0x00; 0x00; 0x00 ]
          @ [ 0x0f; 0x05 ]
          (*
          popq    %rax
          popq    %rdx
          popq    %rsi
          popq    %rdi
          *)
          @ [ 0x58; 0x5a; 0x5e; 0x5f ])
    | Input :: rest ->
        compile' rest
          (acc
           (*
          pushq   %rdi
          pushq   %rsi
          pushq   %rdx
          pushq   %rax
          *)
         @ [ 0x57; 0x56; 0x52; 0x50 ]
         (*
          xor     %eax, %eax
          movq    %rdi, %rsi
          xor     %edi, %edi
          movl    $1, %edx
          syscall
          *)
         @ [ 0x31; 0xc0 ]
          @ [ 0x48; 0x89; 0xfe ] @ [ 0x31; 0xff ]
          @ [ 0xba; 0x01; 0x00; 0x00; 0x00 ]
          @ [ 0x0f; 0x05 ]
          (*
          popq    %rax
          popq    %rdx
          popq    %rsi
          popq    %rdi
          *)
          @ [ 0x58; 0x5a; 0x5e; 0x5f ])
    | Loop sub :: rest ->
        let loop = compile' sub [] in
        let loop_size = List.length loop in
        compile' rest
          (acc
         (*begin:
           cmpb    $0, (%rdi)*)
         @ [ 0x80; 0x3f; 0x00 ]
          (* je      end *)
          @ [ 0x0f; 0x84 ]
          @ int_to_bytes (loop_size + 5) 4
          @ loop
          (*jmp     begin
            end:*)
          @ [ 0xe9 ]
          @ int_to_bytes (0xffffffff - loop_size - 13) 4)
  in
  let prologue =
    (* sub $0x10000, %rsp *)
    [ 0x48; 0x81; 0xec; 0x00; 0x00; 0x01; 0x00 ]
    (* mov %rsp, %rdi *)
    @ [ 0x48; 0x89; 0xe7 ]
  in
  let epilogue =
    (* syscall exit(0) *)
    (* mov $60, %rax *)
    [ 0xb8; 0x3c; 0x00; 0x00; 0x00 ]
    (* mov $0, %rdi *)
    @ [ 0x48; 0x31; 0xff ]
    (* syscall *)
    @ [ 0x0f; 0x05 ]
  in
  compile' instructions prologue @ epilogue |> List.map Char.chr

let make_elf binarycode =
  let file_size = 64 + 56 + List.length binarycode in
  let elf_header =
    [ 0x7f; 0x45; 0x4c; 0x46; 0x02; 0x01; 0x01; 0x00 ]
    @ int_to_bytes 0x000000 8 (* Signature *)
    @ [ 0x03; 0x00; 0x3e; 0x00; 0x01; 0x00; 0x00; 0x00 ] (* Type: executable *)
    @ int_to_bytes 0x400078 8 (* Entry point *)
    @ int_to_bytes 0x000040 8 (* Phdr offset *)
    @ int_to_bytes 0x000000 8 (* Shdr offset *)
    @ [ 0x00; 0x00; 0x00; 0x00 ] (* Flags *)
    @ [ 0x40; 0x00 ] (* ELF header size *)
    @ [ 0x38; 0x00 ] (* Program header size *)
    @ [ 0x01; 0x00 ] (* Number of program headers *)
    @ [ 0x40; 0x00 ] (* Section header size *)
    @ [ 0x00; 0x00 ] (* Number of section headers *)
    @ [ 0x00; 0x00 ]
    (* Shdr string table index *)
    |> List.map Char.chr
  in
  let program_header =
    [ 0x01; 0x00; 0x00; 0x00 ] (* Type: load *)
    @ [ 0x05; 0x00; 0x00; 0x00 ] (* Flags: r-x *)
    @ int_to_bytes 0x000000 8 (* Offset in file *)
    @ int_to_bytes 0x400000 8 (* Virtual address *)
    @ int_to_bytes 0x400000 8 (* Physical address *)
    @ int_to_bytes file_size 8 (* File size *)
    @ int_to_bytes file_size 8 (* Memory size *)
    @ int_to_bytes 0x200000 8 (* Alignment *)
    |> List.map Char.chr
  in
  [ elf_header; program_header; binarycode ] |> List.concat

let usage () =
  Printf.printf "Usage: %s [dump|interpret|compile] <filename>\n" Sys.argv.(0);
  exit 1

let process_file filename =
  let file = open_in filename in
  let buf = really_input_string file (in_channel_length file) in
  close_in file;
  String.to_seq buf |> List.of_seq |> parse |> merge_consecutive

let () =
  if Array.length Sys.argv < 3 then usage ();
  let command = Sys.argv.(1) in
  let filename = Sys.argv.(2) in
  let instructions = process_file filename in
  match command with
  | "dump" -> dump instructions
  | "interpret" -> interpret instructions |> ignore
  | "compile" ->
      let binarycode = compile instructions in
      let binarycode = make_elf binarycode in
      let fd =
        Unix.openfile "a.out"
          [ Unix.O_WRONLY; Unix.O_CREAT; Unix.O_TRUNC ]
          0o755
      in
      Unix.write fd
        (Bytes.of_seq (List.to_seq binarycode))
        0 (List.length binarycode)
      |> ignore;
      Unix.close fd
  | _ -> usage ()
