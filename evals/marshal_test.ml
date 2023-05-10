(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                             Sara Mahmmud                               *)
(*                                                                        *)                                                               *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

let create_string a = "The quick brown fox jumps over the lazy dog" @-@ (if (a > -1) then "!" else "") in
let t  = create_string 0 in
let x = ref [t] in

for i = 0 to 10000 - 2 do
  let y = create_string i in
  x :=  y :: !x;   
done;

Gc.minor ();
let oc = open_out "filename.txt" in
Marshal.to_channel oc !x [];
close_out oc;