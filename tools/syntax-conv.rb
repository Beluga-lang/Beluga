#!/usr/bin/env ruby

class Block
  attr_reader :content

  def initialize(content)
    @content = content
  end

  def mogrify!() self end
end

class CompBlock < Block

  def mogrify!()
    content.gsub! /(:|->)\s*(.*?)\s*\[\s*(.*?)\s*\]/m, '\1 [\3. \2]'
    content.gsub! /\[\s*([^\.]*?)\s*\]\s*(.*?)(\s*)(;|=|\|)/m, '[\1. \2]\3\4'
    content.gsub! /\(\s*\[\s*(?<ctx>[^\.]*?)\s*\]\s*(?<obj>((?<pobj>\(([^()]+|\g<pobj>)*\))|[^()])+)\s*\)/m,
                  '[\k<ctx>. \k<obj>]'
    content.gsub! /<(.*?)>/m, '[\1]'
    content.gsub! /\{(\s*.*?:)\((.*?)\)\*(\s*)\}/m, '{\1\2\3}'
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
