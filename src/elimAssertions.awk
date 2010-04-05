BEGIN {
    inAssertion = 0;
}

/\/\/-BEGIN-ASSERTION-/ {
    inAssertion = 1;
    next;
}

/\/\/-END-ASSERTION-/ {
    inAssertion = 0;
    next;
}

{
    if (!inAssertion) {
        print $0;
    }
}