BEGIN {
    inAssertion = 0;
}

/\/\/-END-ASSERTION-/ {
    inAssertion = 0;
}

{
    if (inAssertion) {
        printf("// %s\n", $0);
    } else {
        print $0;
    }
}

/\/\/-BEGIN-ASSERTION-/ {
    inAssertion = 1;
}
