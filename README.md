itsy-linux
==========

Unix (Linux & MacOS X) port of itsy Forth by John Metcalf

John Metcalf (http://www.retroprogramming.com/) implemented minimal forth system:
<ul>
<li>http://www.retroprogramming.com/2012/03/itsy-forth-1k-tiny-compiler.html </li>
<li>http://www.retroprogramming.com/2012/04/itsy-forth-dictionary-and-inner.html </li>
<li>http://www.retroprogramming.com/2012/04/itsy-forth-primitives.html </li>
<li>http://www.retroprogramming.com/2012/06/itsy-forth-compiler.html </li>
<li>http://www.retroprogramming.com/2012/09/itsy-documenting-bit-twiddling-voodoo.html </li>
</ul>
Resulting binary has very impressive size (978 bytes on Linux) and can be used to bootstrap a complete Forth system.

Original itsy code is producing .com files and can be found in "msdos" directory of this repository.

kt97679 ported it to 32-bit linux code. 
DylanMc ported it to MacOS (also 32 bit). Should move to any BSD pretty easily.

Sample session:

<pre>
$ make
nasm itsy-linux.asm -fbin -l itsy-linux.lst -o itsy-linux
chmod +x itsy-linux
$ ./itsy-linux 
: say_hi 72 emit 105 emit 33 emit 10 emit ;
say_hi
Hi!
^C
$ 
</pre>

TODO:
<ul>
<li> get string literals going </li>
<li> implement string operations, like ." </li>
<li> implement number->string </li>
<li> implement . </li>
<li> if then </li>
<li> do .. loop </li>
</ul>
