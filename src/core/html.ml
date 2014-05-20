let genHtml = ref false
let indent = ref 0

let spacess : string =	String.make (!indent) ' '

let page = ref ""

let generatePage filename = 
begin
	let oc = open_out filename in
	output_string oc  (!page ^ "\n");
	close_out oc	
end

let appendAsAnchor innerHtml id =
	page := (!page) ^ "\n" ^ spacess ^ "<p id=" ^ id ^ ">" ^ innerHtml ^ "</p>"

let appendAsLink innerHtml id =
	page := (!page) ^ "\n" ^ spacess ^ "<a href=#" ^ id ^ ">" ^ innerHtml ^ "</a>"

let append innerHtml =
	page := (!page) ^ "\n" ^ spacess ^ "<p>" ^ innerHtml ^ "</p>"
