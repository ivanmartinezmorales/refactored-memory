const Viz = require('viz.js');

$('document').ready(
    function () {
        let $input = $('#input');
        let $language = $('#language');
        let $graph = $('#graph');
        let $submit = $('#submit');

        $input.on('input', function () {
            var re = $input.val();
            var charset = parseCharset(re);
            $language.val(charset);
        });

        $('form').submit(function(event) {
            event.preventDefault();
            const fsmType = $('input:checked').val();
            const language = $language.val();
            const regularExpression = $input.val();
            const regularExpressionTree = regularExpressionParser(regularExpression, language);
            const nfaStateDiagram = NFA.fromRegexTree(regularExpressionTree, language);
            console.log(nfaStateDiagram);
            let visualization = null;

            switch (fsmType) {
                case "nfa":
                    var dotScript = nfaToDotScript(nfaStateDiagram);
                    visualization = Viz(dotScript);
                    break;

                case "dfa":
                    var dfaDotScript = dfaToDotScript(DFA.fromNFA(nfaStateDiagram, language));
                    visualization = Viz(dfaDotScript)
                    break;

                default:
                    break;
            }
            console.log(visualization);
            $graph.html(visualization);
        });
    }
)

let parseCharset = function (v) {
    v = v.replace(/[^a-zA-Z0-9]+/g, '');
    v = v.split('').sort();
    v = Array.from(new Set(v));
    v = v.join(' ');

    return v;
};

function nfaToDotScript(nfa) {
    var initialState = nfa.initialState;
    var finalState = nfa.finalState;

    var result = `
digraph nondeterministic_finite_automaton {
    rankdir = LR;
    node [shape = circle]; ${initialState};
    node [shape = doublecircle]; ${finalState};
    node [shape = plaintext];
    "" -> ${initialState} [label = "start"];
    node [shape = circle];
`;

    for (var p in nfa._transitions) {
        var node = nfa._transitions[p];
        for (var accept in node) {
            for (var i in node[accept]) {
                var q = node[accept][i];
                result += `    ${p} -> ${q} [label="${accept}"]\n`;
            }
        }
    }
    result += '}';

    return result;
};

function dfaToDotScript(dfa) {
    var initialState = dfa.initialState;
    var finalStates = Array.from(dfa.finalStates).join(', ');

    var result = `
digraph deterministic_finite_automaton {
    rankdir = LR;
`;
    if (!dfa.finalStates.has(initialState)) {
        result += `    node [shape = circle]; ${initialState};\n`;
    }
    result += `    node [shape = doublecircle]; ${finalStates};
    node [shape = plaintext];
    "" -> ${initialState} [label = "start"];
    node [shape = circle];
`;

    for (var p in dfa._transitions) {
        for (var accept in dfa._transitions[p]) {
            var q = dfa._transitions[p][accept];
            result += `    ${p} -> ${q} [label="${accept}"]\n`;
        }
    }
    result += '}';

    return result;
};

function regularExpressionParser(expr, charset) {
    var pos = 0;

    var eval = function () {
        var terms = [term()];
        while (expr[pos] == '|') {
            pos++;
            terms.push(term());
        }

        if (terms.length > 1) {
            return { 'or': terms };
        } else if (terms.length == 1) {
            return terms[0];
        } else {
            return null;
        }
    };

    var isFactor = function (s) {
        return charset.indexOf(s) !== -1 || s == '(';
    }

    var term = function () {
        var factors = [factor()];
        while (expr[pos] == '&' || isFactor(expr[pos])) {
            if (!isFactor(expr[pos])) {
                pos++;
            }

            factors.push(factor());
        }

        if (factors.length > 1) {
            return { 'and': factors };
        } else if (factors.length == 1) {
            return factors[0];
        } else {
            return null;
        }
    };

    var factor = function () {
        var r = 0;
        if (expr[pos] == '(') {
            pos++;
            r = eval();
            pos++;
        } else {
            r = expr[pos];
            pos++;
        }

        if (expr[pos] == '*') {
            r = { 'star': r };
            pos++;
        }

        return r;
    };

    return eval();
};

var numCmp = function(x, y) {
    return x - y;
};

var Conceal = {};
Conceal._list = {};
Conceal._assoc = {};
Conceal._idx = 0;
Conceal.stringify = function(v) {
    var key = JSON.stringify(v);
    if (key in Conceal._assoc) {
        return Conceal._assoc[key];
    }

    Conceal._assoc[key] = Conceal._idx;
    Conceal._list[Conceal._idx] = v;

    return this._idx++;
};
Conceal.parse = function(id) {
    return Conceal._list[id];
};

// Debugging purposes
// Conceal = JSON;

var DFA = function(charset, initialState) {
    this.initialState = initialState;
    this.finalStates = new Set();
    this.charset = charset || '';
    this._transitions = {};
    this._state = 0;
};

DFA.fromNFA = function(nfa, charset) {
    var dfa = new this(charset);
    dfa._fromNFA(nfa);

    return dfa;
}

DFA.prototype.newState = function() {
    this._transitions.push({});

    return this._state++;
};

DFA.prototype.addTransition = function(from, to, accept) {
    if (!(from in this._transitions)) {
        this._transitions[from] = {};
    }

    this._transitions[from][accept] = to;
};

DFA.prototype.isFinalState = function(state) {
    return this.finalStates.has(state);
}

DFA.prototype.check = function(s) {
    var self = this;
    var _dfs = function(state, pos) {
        if (pos == s.length && self.isFinalState(state)) {
            return true;
        }

        var accept = s[pos];
        if (state in self._transitions && accept in self._transitions[state]) {
            var newState = self._transitions[state][accept];
            if (_dfs(newState, pos + 1)) {
                return true;
            }
        }

        return false;
    };

    return _dfs(this.initialState, 0);
};

DFA.prototype._fromNFA = function(nfa) {
    var epsClosure = function(state, states) {
        var states = new Set([state]);
        var Q = [state];
        while (Q.length > 0) {
            var p = Q.shift();
            if (!(p in nfa._transitions) ||
                !(NFA.EPS in nfa._transitions[p])
            ) {
                continue;
            }

            for (var q of nfa._transitions[p][NFA.EPS]) {
                if (!states.has(q)) {
                    states.add(q);
                    Q.push(q);
                }
            }
        }

        states = Array.from(states).sort(numCmp);

        return states;
    };


    // To obtain a DFA M = < Q,  , q0 , , A > which accepts the same language as the given NFA M2 = < Q2 ,  , q2,0 , 2 , A2 > does, you may proceed as follows:

    this.charset = nfa.charset;
    console.log(this.charset);

    // Initially Q = null.
    var Q = [];
    var marked = {};

    this.initialState = Conceal.stringify(epsClosure(nfa.initialState));
    // First put { q2,0 } into Q. { q2,0 } is the initial state of the DFA M.
    Q.push(this.initialState);
    // Then for each state q in Q do the following:
    while (Q.length > 0) {
        var state = Q.shift();
        if (marked[state]) {
            continue;
        }

        var nfaStates = Conceal.parse(state);
        for (var p of nfaStates) {
            if (nfa.isFinalState(p)) {
                this.finalStates.add(state);
                break;
            }
        }

        // add the set , where here is that of NFA M2, as a state to Q if it is not already in Q for each symbol a in  .
        for (var a of this.charset) {
            var newState = [];
            for (var p of nfaStates) {
                if (!(p in nfa._transitions)
                    || !(a in nfa._transitions[p])
                ) {
                    continue;
                }

                newState = newState.concat(nfa._transitions[p][a]);
            }

            if (newState.length == 0) {
                continue;
            }

            newState = new Set(newState);
            newState = Array.from(newState).reduce(function(acc, val) {
                return acc.concat(epsClosure(val));
            }, []);
            newState = new Set(newState);
            newState = Array.from(newState).sort(numCmp);
            newState = Conceal.stringify(newState);

            // For this new state, add ( q, a ) =   to  , where the  on the right hand side is that of NFA M2.
            this.addTransition(state, newState, a);
            if (marked[newState] !== true) {
                Q.push(newState);
            }
        }

        marked[state] = true;
    }

    // When no more new states can be added to Q, the process terminates. All the states of Q that contain accepting states of M2 are accepting states of M.
};

var NFA = function(charset, initialState, finalState) {
    this.initialState = initialState;
    this.finalState = finalState;
    this.charset = charset || '';
    this._transitions = [];
    this._state = 0;
};
NFA.EPS = 'ε';

NFA.fromRegexTree = function(tree, charset) {
    var nfa = new this(charset);
    var states = nfa._fromRegexTree(tree);
    nfa.initialState = states.initialState;
    nfa.finalState = states.finalState;

    return nfa;
};

NFA.prototype.newState = function() {
    this._transitions.push({});

    return this._state++;
};

NFA.prototype.isFinalState = function(state) {
    return this.finalState === state;
};

NFA.prototype.addTransition = function(from, to, accept) {
    accept = accept || NFA.EPS;
    if (!this._transitions[from][accept]) {
        this._transitions[from][accept] = [];
    }

    this._transitions[from][accept].push(to);
};

NFA.prototype.check = function(s) {
    var self = this;
    var _dfs = function(state, pos) {
        if (pos == s.length && self.isFinalState(state)) {
            return true;
        }

        for (var accept of [NFA.EPS, s[pos]]) {
            if (!(accept in self._transitions[state])) {
                continue;
            }

            var newPos = pos + (accept !== NFA.EPS);
            for (var newState of self._transitions[state][accept]) {
                if (_dfs(newState, newPos)) {
                    return true;
                }
            }
        }

        return false;
    };

    return _dfs(this.initialState, 0);
};

NFA.prototype._fromRegexTree = function(tree) {
    var initialState = this.newState();
    var finalState = this.newState();
    if (typeof(tree) !== 'object') {
        var accept = tree;
        this.addTransition(initialState, finalState, accept);
    } else if ('or' in tree) {
        for (var leaf of tree['or']) {
            var nfa = this._fromRegexTree(leaf);
            this.addTransition(initialState, nfa.initialState);
            this.addTransition(nfa.finalState, finalState);
        }
    } else if ('and' in tree) {
        var state = this.newState();
        this.addTransition(initialState, state);
        for (var leaf of tree['and']) {
            var nfa = this._fromRegexTree(leaf);
            this.addTransition(state, nfa.initialState);
            state = nfa.finalState;
        }
        this.addTransition(state, finalState);
    } else if ('star' in tree) {
        this.addTransition(initialState, finalState);

        var state1 = this.newState();
        this.addTransition(initialState, state1);

        var leaf = tree['star'];
        var nfa2 = this._fromRegexTree(leaf);
        this.addTransition(state1, nfa2.initialState);
        this.addTransition(nfa2.finalState, state1);
        this.addTransition(nfa2.finalState, finalState);
    }

    return {
        'initialState': initialState,
        'finalState': finalState,
    };
};
