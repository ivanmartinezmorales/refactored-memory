<!doctype html>
<html lang="en">

<head>
    <!-- Required meta tags -->
    <meta charset="utf-8">
    <meta name="viewport" content="width=device-width, initial-scale=1, shrink-to-fit=no">

    <!-- Bootstrap CSS -->
    <link rel="stylesheet" href="https://stackpath.bootstrapcdn.com/bootstrap/4.5.0/css/bootstrap.min.css"
        integrity="sha384-9aIt2nRpC12Uk9gS9baDl411NQApFmC26EwAOH8WgZl5MYYxFfc+NcPb1dKGj7Sk" crossorigin="anonymous">
    <link rel="stylesheet" href="./style.css">
    <title>REGEX to DFA/NFA</title>
</head>

<body>
    <div class="container m-auto pt-5">
        <div class="py-3">
            <h1>CSE355 Bonus Project</h1>
            <p>Written by Ivan Martinez Morales</p>
        </div>
        <!-- Input Group -->
        <div class="py-3">
            <p>Write out your regular expression below. The right text area will give you a preview of the language</p>
            <form>
                <div class="form-group">
                    <label for="regularExpression">Regular Expression</label>
                    <input type="text" class="form-control" id="input" required>
                    <label for="language" class="pt-2">FSM Alphabet</label>
                    <input class="form-control" type="text" id="language" readonly>
                </div>
                <div class="form-group">
                  <label for="fsm-type">FSM type</label>
                    <div class="form-check">
                        <input class="form-check-input" type="radio" name="fsm-type" id="dfa" value="dfa" checked>
                        <label class="form-check-label" for="dfa">Deterministic Finite Automaton</label>
                    </div>
                    <div class="form-check">
                        <input class="form-check-input" type="radio" name="fsm-type" id="nfa" value="nfa">
                        <label class="form-check-label" for="nfa">Nondeterministic Finite Automaton</label>
                    </div>
                    <button id="submit" class="btn btn-secondary my-3">Create State Diagram!</button>
                </div>
            </form>
        </div>
        <!-- Output graphs -->
        <div id="graph"> </div>
        <!-- Explanation of DFA/NFA-->
    </div>
    <!-- Optional JavaScript -->
    <!-- jQuery first, then Popper.js, then Bootstrap JS -->
    <script src="https://code.jquery.com/jquery-3.5.1.slim.min.js"
        integrity="sha384-DfXdz2htPH0lsSSs5nCTpuj/zy4C+OGpamoFVy38MVBnE+IbbVYUew+OrCXaRkfj" crossorigin="anonymous">
    </script>
    <script src="https://cdn.jsdelivr.net/npm/popper.js@1.16.0/dist/umd/popper.min.js"
        integrity="sha384-Q6E9RHvbIyZFJoft+2mJbHaEWldlvI9IOYy5n3zV9zzTtmI3UksdQRVvoxMfooAo" crossorigin="anonymous">
    </script>
    <script src="https://stackpath.bootstrapcdn.com/bootstrap/4.5.0/js/bootstrap.min.js"
        integrity="sha384-OgVRvuATP1z7JjHLkuOU7Xw704+h835Lr+6QL9UvYjZE3Ipu6Tp75j7Bh/kR0JKI" crossorigin="anonymous">
    </script>
    <script src="bundle.js"></script>
</body>

</html>
