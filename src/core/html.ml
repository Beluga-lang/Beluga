type htmlClass = Kind | Const | None | Fun
let genHtml = ref false
let ids = ref []



let page = ref ""
(* \n\t\tspan {margin: 2em 1em 2em 1em;} *)
let header =
	"<head>
	\n\t<style type=\"text/css\">
	\n\t\tbody {
	\n\t\t\tpadding: 2em 1em 2em 1em;
	\n\t\t\tmargin: 0;
	\n\t\t\tfont-family: sans-serif;
	\n\t\t\tcolor: black;
	\n\t\t\tbackground: white;}
	
	\n\t\t:link { color: #00C; background: transparent }
	\n\t\t:visited { color: #00C; background: transparent }
	\n\t\ta:active { color: #C00; background: transparent }
	\n\t\t.keyword { color: #600000 ; background: transparent }
	\n\t\tcode { display:block; border:1px solid #d4d4d4;background-color:#f1f1f1;color:#444444;padding:5px;margin:0; }
	\n\t</style>
	\n</head>\n"

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

let urlEncode innerHtml =
	let keywords = Str.regexp "\\(rec\\|let\\|case\\|of\\|
							FN\\|and\\|block\\|Bool\\|datatype\\|
							else\\|mlam\\|schema\\|type\\|
							ttrue\\|ffalse\\|%name\\|
							%opts\\|%not\\|%query\\)" in
	let br = Str.regexp_string "\n" in
	let innerHtml = Str.global_replace keywords "<span class=\"keyword\">\\0</span>" innerHtml in
	let innerHtml = Str.global_replace br "<br>" innerHtml in
	innerHtml 
(* 	let l = removeSpaces s in
	String.concat "&nbsp" l *)


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
	let innerHtml = urlEncode innerHtml in
	page := (!page) ^ "\n" ^ "<br><p>" ^ innerHtml ^ "</p>"

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