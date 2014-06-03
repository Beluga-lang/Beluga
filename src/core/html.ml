type htmlClass = Kind | Const | None | Fun
let genHtml = ref false
let ids = ref []


let page = ref ""
(* \n\t\tspan {margin: 2em 1em 2em 1em;} *)
let header =
"<head>" ^
  "<style type=\"text/css\">" ^
    "body {" ^
      "padding: 2em 1em 2em 1em;" ^
      "margin: 0;" ^
      "font-family: sans-serif;" ^
      "color: black;" ^
      "background: white;}" ^
    ":link { color: #00C; background: transparent }" ^
    ":visited { color: #00C; background: transparent }" ^
    "a:active { color: #C00; background: transparent }" ^
    ".keyword { color: #3333cc ; background: transparent }" ^
    "code { display:block; background-color: #dddddd;border: 1px dashed maroon; color: black;font-family: \"courier\";padding:5px;margin:0; }" ^
  "</style>" ^
"</head>\n"

let generatePage filename = 
begin
	let codeRegex = Str.regexp "<div\\(.*?\\)>\\(.*?\\)</div>" in
	let page = Str.global_replace codeRegex "<code><span\\1>\\2</span></code>\n" !page in
	let fixCodeRegex = Str.regexp "</code>\\(\\([\r\n\t]\\|<br>\\)*?\\)<code>" in
	let page = Str.global_replace fixCodeRegex "\\1" page in
	let oc = open_out filename in
	output_string oc header;
	output_string oc "<body>\n";
	output_string oc  (page ^ "\n");
	output_string oc "</body>\n" ;
	close_out oc
end

let replaceNewLine = Str.global_replace (Str.regexp_string "\n") "<br>"

let keywords = "\\(rec\\|let\\|case\\|of\\|FN\\|and\\|block\\|Bool\\|datatype\\"^
			   "|else\\|mlam\\|schema\\|type\\|ttrue\\|ffalse\\|%name\\|%opts\\|" ^ 
			   "%not\\|%query\\|#infix\\|#postifix\\)"
let
 replaceKeyWords = let keywords = Str.regexp keywords in
	Str.global_replace keywords "<span class=\"keyword\">\\0</span>"

let replaceSpace s = Str.global_replace (Str.regexp_string " ") "&nbsp" s

let replaceIDs s = List.fold_right (fun x y -> Str.global_replace 
		(Str.regexp ("\\(:\\|(\\|&nbsp\\)" ^ x ^ "&nbsp")) ("\\1<a href=#" ^ x ^ ">" ^ x ^ "</a>&nbsp") y) !ids s

let urlEncode innerHtml =
	replaceIDs (replaceKeyWords (replaceNewLine (replaceSpace innerHtml)))


let appendAsAnchor innerHtml id htmlClass =
	let innerHtml = urlEncode innerHtml in
	ids := id :: !ids ;
	page := (!page) ^ "\n" ^  "<br><div id=" ^ id ^ 
			(match htmlClass with
				| Kind -> " class=\"kind\" "
				| Const -> " class=\"const\" "
				| Fun -> " class=\"fun\" "
				| _ -> "")
			^ ">" ^ innerHtml ^ "</div>\n"

(* let appendAsLink innerHtml id =
	page := (!page) ^ "\n" ^ spaces ^ "<a href=#" ^ id ^ ">" ^ innerHtml ^ "</a>" *)

let append innerHtml =
	let innerHtml = urlEncode innerHtml in
	page := (!page) ^ "\n"  ^ "<br><div>" ^ innerHtml ^ "</div>"

let appendAsComment innerHtml = 
	let innerHtml = Str.global_replace (Str.regexp "\\(%{\\|}%\\)") "" innerHtml in
	let innerHtml = replaceNewLine innerHtml in
	page := (!page) ^ "\n" ^ "<p>" ^ innerHtml ^ "</p>"

(********************
	TODO:
		- make constructor names bold / other color?
		- add linking within pages



*)
(* let turnstile = '⊢'

let arrow = '→'

let arrow2 = '⇒'

let fix str =
	let aux s c1 c2 i c = 
		if c = c1 && str.[i+1] = c2 then
		str.[i] <- s ; str.[i+1] <- ' ' 
	in
	String.iteri (aux '⊢' '|' '-') str ;
	String.iteri (aux '→' '-' '>') str ;
	String.iteri (aux '⇒' '=' '>') str ;
	str
	let _ = String.iteri (fun i c -> if c = '|' && s.[i+1] = '-' then (String.set s i '⊢' ; String.set s (i+1) ' ')) s in
	let _ = String.iteri (fun i c -> if c = '-' && s.[i+1] = '>' then (let _ = String.set s i  '→' in let _ = String.set s (i+1)  ' ' in ())) s in
	let _ = String.iteri (fun i c -> if c = '=' && s.[i+1] = '>' then (let _ = String.set s i  '⇒' in let _ = String.set s (i+1)  ' ' in ())) s in
	str *)