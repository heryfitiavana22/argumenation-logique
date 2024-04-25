type Proposition = { value: string; no?: boolean };
type PropositionComposed = {
  operand1: Proposition;
  operator: Operator;
  operand2: Proposition;
  no?: boolean;
};

type Operator = "=>" | "^" | "V";

type Hypothesis = {
  operand1: Proposition | PropositionComposed;
  operator?: Operator;
  operand2?: Proposition | PropositionComposed;
};

function isPropositionType(
  p: Proposition | PropositionComposed
): p is Proposition {
  return typeof p === "object" && "value" in p;
}

function isSameProposition(
  p1: Proposition | PropositionComposed,
  p2: Proposition | PropositionComposed
) {
  if (p1.no == undefined) p1.no = false;
  if (p2.no == undefined) p2.no = false;
  if (
    isPropositionType(p1) &&
    isPropositionType(p2) &&
    p1.value === p2.value &&
    p1.no == p2.no
  )
    return true;

  return JSON.stringify(p1) == JSON.stringify(p2);
}
function isSameHypothesis(h1: Hypothesis, h2: Hypothesis) {
  if (h1.operand2 && h2.operand2)
    return (
      isSameProposition(h1.operand1, h2.operand1) &&
      isSameProposition(h1.operand2, h2.operand2)
    );

  if (h1.operand2 || h2.operand2) return false;
  return isSameProposition(h1.operand1, h2.operand1);
}

function isImplication(h: Hypothesis) {
  return h.operator === "=>" && h.operand2;
}
function isNo(p: Proposition | PropositionComposed) {
  return p.no;
}
function isTransitivity(h1: Hypothesis, h2: Hypothesis) {
  return (
    isImplication(h1) &&
    isImplication(h2) &&
    h1.operand2 &&
    isSameProposition(h1.operand2, h2.operand1)
  );
}
function transitivity(h1: Hypothesis, h2: Hypothesis): Hypothesis | null {
  if (isTransitivity(h1, h2))
    return { operand1: h1.operand1, operator: "=>", operand2: h2.operand2 };
  return null;
}

function modusTollens(h1: Hypothesis, h2: Hypothesis): Hypothesis | null {
  if (
    isImplication(h1) &&
    h1.operand2 &&
    isSameProposition(
      { ...h1.operand2, no: true },
      { ...h2.operand1, no: true }
    ) &&
    isNo(h2.operand1) &&
    h2.operator == undefined
  ) {
    if (isPropositionType(h1.operand1))
      return {
        operand1: { ...h1.operand1, no: !h1.operand1.no },
      };
    h1.operand1.no = !h1.operand1.no;
    return { ...h1.operand1 };
  }

  if (
    isImplication(h2) &&
    h2.operand2 &&
    isSameProposition(
      { ...h1.operand1, no: true },
      { ...h2.operand2, no: true }
    ) &&
    isNo(h1.operand1) &&
    h1.operator == undefined
  ) {
    if (isPropositionType(h2.operand1))
      return {
        operand1: { ...h2.operand1, no: !h2.operand1.no },
      };
    h2.operand1.no = !h2.operand1.no;
    return { ...h2.operand1 };
  }
  return null;
}

function modusPonens(h1: Hypothesis, h2: Hypothesis): Hypothesis | null {
  if (
    isImplication(h2) &&
    isSameProposition(h1.operand1, h2.operand1) &&
    h2.operand2 &&
    h1.operator == undefined
  ) {
    if (isPropositionType(h2.operand2))
      return {
        operand1: { ...h2.operand2 },
      };
    return { ...h2.operand2 };
  }

  if (
    isImplication(h1) &&
    isSameProposition(h1.operand1, h2.operand1) &&
    h1.operand2 &&
    h2.operator == undefined
  ) {
    if (isPropositionType(h1.operand2))
      return {
        operand1: { ...h1.operand2 },
      };
    return { ...h1.operand2 };
  }
  return null;
}

function orToImplication(h: Hypothesis): Hypothesis | null {
  if (h.operator == "V" && h.operand2) {
    return {
      operand1: { ...h.operand1, no: !h.operand1.no },
      operator: "=>",
      operand2: h.operand2,
    };
  }
  return null;
}

function contrapositivity(h: Hypothesis): Hypothesis | null {
  if (isImplication(h) && h.operand2)
    return {
      operand1: { ...h.operand2, no: !h.operand2.no },
      operator: "=>",
      operand2: { ...h.operand1, no: !h.operand1.no },
    };

  return null;
}

function valid(hypothesis: Hypothesis[]) {
  let args = [...hypothesis];
  let running = true;

  while (args.length > 1 && running) {
    let i = 0;
    for (let i = 0; i < args.length; i++) {
      let hyp1 = orToImplication(args[i]) || args[i];
      for (let j = 0; j < args.length; j++) {
        let hyp2 = orToImplication(args[j]) || args[j];
        if (isSameHypothesis(hyp1, hyp2)) continue;

        function updateArgs(h1: Hypothesis, h2: Hypothesis) {
          let newHyp = infenrenceRules({ h1, h2 });
          function onNewHyp(h: Hypothesis, i: number, j: number) {
            return [
              h,
              ...args.filter((curr, index) => ![i, j].includes(index)),
            ];
          }

          if (newHyp) {
            args = onNewHyp(newHyp, i, j);
            if (args.length == 1) running = false;
            return true;
          }

          const cph1 = contrapositivity(h1);
          if (cph1) {
            newHyp = infenrenceRules({ h1: cph1, h2: h2 });
            if (newHyp) {
              args = onNewHyp(newHyp, i, j);
              if (args.length == 1) running = false;
              return true;
            }
          }
          const cpH2 = contrapositivity(h2);
          if (cpH2) {
            newHyp = infenrenceRules({ h1, h2: cpH2 });
            if (newHyp) {
              args = onNewHyp(newHyp, i, j);
              if (args.length == 1) running = false;
              return true;
            }
          }
        }
        if (hyp1.operator == "^" && hyp1.operand2) {
          if (updateArgs({ operand1: hyp1.operand1 }, hyp2)) break;
          if (updateArgs({ operand1: hyp1.operand2 }, hyp2)) break;
        }
        if (hyp2.operator == "^" && hyp2.operand2) {
          if (updateArgs(hyp1, { operand1: hyp2.operand1 })) break;
          if (updateArgs(hyp1, { operand1: hyp2.operand2 })) break;
        }
        if (updateArgs(hyp1, hyp2)) break;
      }
      if (!running) break;
    }
  }
  return args[0];
}

function infenrenceRules({ h1, h2 }: InfenrenceRulesParams) {
  const newHyp =
    modusPonens(h1, h2) ||
    modusTollens(h1, h2) ||
    transitivity(h1, h2) ||
    transitivity(h2, h1);
  return newHyp;
}
type InfenrenceRulesParams = {
  h1: Hypothesis;
  h2: Hypothesis;
};

const exo1: Hypothesis[] = [
  { operand1: { value: "p" } },
  { operand1: { value: "p" }, operator: "=>", operand2: { value: "q" } },
  { operand1: { value: "q" }, operator: "=>", operand2: { value: "r" } },
];
const exo2: Hypothesis[] = [
  { operand1: { value: "p" }, operator: "=>", operand2: { value: "r" } },
  { operand1: { value: "r" }, operator: "=>", operand2: { value: "s" } },
  {
    operand1: { value: "t" },
    operator: "V",
    operand2: { value: "s", no: true },
  },
  {
    operand1: { value: "t", no: true },
    operator: "V",
    operand2: { value: "u" },
  },
  { operand1: { value: "u", no: true } },
];
const exo3: Hypothesis[] = [
  { operand1: { value: "p" }, operator: "=>", operand2: { value: "r" } },
  {
    operand1: { value: "p", no: true },
    operator: "=>",
    operand2: { value: "q" },
  },
  { operand1: { value: "q" }, operator: "=>", operand2: { value: "s" } },
];

console.log("Result : ");
console.log(valid(exo3));
