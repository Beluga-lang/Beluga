let genHtml = ref false
let indent = ref 0

let spacess : string =	String.make (!indent) ' '

let page = ref ""

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
	\n\t\t:visited { color: #609; background: transparent }
	\n\t\ta:active { color: #C00; background: transparent }
	\n\t</style>
	\n</head>\n"


(********************
	TODO:
		- make constructor names bold / other color?
		- add linking within pages



*)
let generatePage filename = 
begin
	let oc = open_out filename in
	output_string oc header;
	output_string oc "<body>\n";
	output_string oc  (!page ^ "\n");
	output_string oc "</body>\n" ;
	close_out oc	
end

let appendAsAnchor innerHtml id =
	page := (!page) ^ "\n" ^ spacess ^ "<p id=" ^ id ^ ">" ^ innerHtml ^ "</p>"

let appendAsLink innerHtml id =
	page := (!page) ^ "\n" ^ spacess ^ "<a href=#" ^ id ^ ">" ^ innerHtml ^ "</a>"

let append innerHtml =
	page := (!page) ^ "\n" ^ spacess ^ "<p>" ^ innerHtml ^ "</p>"
