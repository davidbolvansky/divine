. lib

normal() {
    diff -u out.dot $1.dot
}

labels() {
    grep '\->' out.dot | not grep -v '\[.*label.*\]'
}

test "$WIN32" = "1" && skip

extracheck=normal
dve_small draw -r cat -o out.dot

extracheck=labels
dve_small draw -l -r cat -o out.dot
