extends Node

# Code before off/on region is formatted normally
var   badly_spaced_var  =   10

# gdformat: off
var   preserved_var   =   20
var preserved_dict   =   {
		"key1":    "value1",
  "key2":"value2",
}
# gdformat: on

var   another_var  =  30


# gdformat: off
var   unformatted_a  =  1
var   unformatted_b  =  2
# gdformat: on


func   formatted_func():
	var   a   =   1
	var   b   =   2
	pass


# Off/on inside an indented block
class InnerClass:
	# gdformat: off
	var   inner_preserved   =   "hello"
	var   inner_preserved_2   =   "world"
	# gdformat: on

	var   inner_formatted  =   "formatted"


# Off without on extends to EOF
# gdformat: off
var   eof_var   =   100
func   eof_func():
	var   x  =   "preserved to eof"
