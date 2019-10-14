# Transform anything that looks like \AgdaZZZ{xyz34}, i.e. an
# Agda identifier with trailing digits, into something like
# \AgdaZZZ{xyz$_{34}$}, where the digits are typeset as
# subscripts.

s/\\Agda\([a-zA-Z]\+\){\([a-zA-Z]\+\)\([0-9]\+\)}/\\Agda\1{\2$_{\3}$}/g

