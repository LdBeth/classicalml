let phi f = 
  let ff arg =
    print_tok `entering`;
    (let res = f arg in
       print_tok `leaving`;
       res
    ) in
      (ff, ());;
