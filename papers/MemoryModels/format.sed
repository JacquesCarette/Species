# Transform anything that looks like \AgdaFunction{xyz34}, i.e. an
# Agda identifier with trailing digits, into something like
# \AgdaFunction{xyz$_{34}$}, where the digits are typeset as
# subscripts.

s/\\AgdaFunction{\([a-zA-Z]\+\)\([0-9]\+\)}/\\AgdaFunction{\1$_{\2}$}/g

