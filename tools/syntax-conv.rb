#!/usr/bin/env ruby

class String
  def gsub_ignore_comments!(pat, replacement)
    pat = Regexp.new("(?:(?<comment>(?m:%\{.*?\}%)|%.*?$)|#{pat.source})", pat.options)
    current, post = "", self
    while pat =~ post do
      pre, s, post = $`, $&, $'
      s.gsub!(pat, replacement) unless $~[:comment]
      current <<= pre << s
    end
    self.replace (current << post)
  end
end

class Block
  attr_reader :content

  def initialize(content)
    @content = content
  end

  def mogrify!() self end
end

class CompBlock < Block

  def mogrify!()
    content.gsub!(/(?<leadin>(::|->|:|\})\s*)(?<obj>[^\{\}]*?)\s*\[\s*(?<ctx>.*?)\s*\]/m, '\k<leadin> [\k<ctx>. \k<obj>]')
    content.gsub! /\(\s*\[\s*(?<ctx>[^\.]*?)\s*\]\s*(?<obj>((?<pobj>\(([^()]+|\g<pobj>)*\))|[^()])+)\s*\)/m,
                  '[\k<ctx>. \k<obj>]'
    content.gsub! /(?<leadin>=\s*)\[\s*(?<ctx>[^\.\[\]%]*)\s*\]\s*(?<obj>[^\[\]]*?)(?<leadout>\s*in)/m, '\k<leadin>[\<ctx>. \k<obj>]\k<leadout>'
    content.gsub! /(?<leadin>case\s*)\[\s*(?<ctx>[^\.\[\]%]*)\s*\]\s*(?<obj>[^\[\]]*?)(?<leadout>\s*of)/m, '\k<leadin>[\k<ctx>. \k<obj>]\k<leadout>'
    content.gsub! /\[\s*(?<ctx>[^\.\[\]%]*)\s*\]\s*(?<obj>[^\[\]]*?)(?<leadout>\s*(;|=>|=|\|))/m, '[\k<ctx>. \k<obj>]\k<leadout>'
    content.gsub! /<(?<cobj>.*?)>/m, '[\k<cobj>]'
    content.gsub! /\{(?<ctx>\s*.*?:\s*)\((?<ctxtyp>.*?)\)\*\s*\}/m, '{\k<ctx>\k<ctxtyp>}'
    content.gsub! /FN/, 'mlam'
    content.gsub! /::/, ':'
    self
  end
end

if ARGV.length < 1 or ARGV.length > 2 then
    $stderr.puts "Usage: #{File.basename( $0 )} file.bel"
    exit 1
end

content = File.read ARGV.pop
block = CompBlock.new content
block.mogrify!
puts block.content
