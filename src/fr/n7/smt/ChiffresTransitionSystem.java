package fr.n7.smt;

import java.math.BigInteger;
import java.util.Arrays;

import com.microsoft.z3.*;

/**
 * Transition system for the "Countdown" game a.k.a. "des chiffres
 * et des lettres" in French.
 *
 * @author Christophe Garion <christophe.garion@isae-supaero.fr>
 * @author Rémi Delmas <remi.delmas@onera.fr>
 *
 */
public class ChiffresTransitionSystem extends TransitionSystem {

    private Context       context;
    private ChiffresCache cache;
    private int           bvBits;
    private int[]         nums;
    private int           target;
    private int           maxNofSteps;
    private boolean       noOverflows;

    // minmum and maximum values for bitvectors
    private BigInteger    maxBvRange;
    private BigInteger    minBvRange;

    private BitVecNum toBvNum(int num) {
        if (noOverflows) {
            BigInteger bigNum = new BigInteger(String.valueOf(num));

            if (bigNum.compareTo(minBvRange) >= 0 && bigNum.compareTo(maxBvRange) <= 0)
                return context.mkBV(num, bvBits);
            else
                throw new Error("the numeral " + String.valueOf(num) +
                                " exceed signed bitvectors of size " +
                                String.valueOf(bvBits));
        } else {
            return context.mkBV(num, bvBits);
        }
    }

    /**
     * Creates a new Chiffres transition system
     *
     * @param nums an array with the starting integers
     * @param target the target integer
     * @param bvBits the number of bits in bitvectors
     * @param noOverflows a boolean that is true if you do not want
     *        overflows with bitvectors
     */
    public ChiffresTransitionSystem(int[] nums, int target, int bvBits, boolean noOverflows) {
        this.context     = Z3Utils.getZ3Context();
        this.cache       = new ChiffresCache(bvBits);
        this.nums        = nums;
        this.target      = target;
        this.bvBits      = bvBits;
        this.maxBvRange  = new BigInteger("2").pow(bvBits-1).subtract(new BigInteger("1"));
        this.minBvRange  = new BigInteger("2").pow(bvBits-1).negate();

        // TODO: to complete!
        this.maxNofSteps = Math.max(2*nums.length - 1,0);

        this.noOverflows = noOverflows;
    }

    /**
     * Gets the maximum number of steps of the transition system.
     *
     */
    public int getMaxNofSteps() {
        return this.maxNofSteps;
    }

    @Override
    public BoolExpr initialStateFormula() {
        return context.mkEq(cache.idxStateVar(0), context.mkInt(0));
    }

    @Override
    public BoolExpr finalStateFormula(int step) {
        IntExpr idx = cache.idxStateVar(step);
        BoolExpr hasOneElement = context.mkEq(idx, context.mkInt(1));

        
        ArrayExpr<IntSort, BitVecSort> stack = cache.stackStateVar(step);
        BitVecExpr top = (BitVecExpr) context.mkSelect(stack, context.mkInt(0));
        BitVecNum expected = toBvNum(target);
        BoolExpr topIsExpected = context.mkEq(top, expected);

        return context.mkAnd(hasOneElement,topIsExpected);
    }

    /**
     * A boolean formula that should be true iff states at step and
     * step + 1 are linked by a "push(num)" action.
     */
    private BoolExpr pushNumFormula(int step, int num) {        
        IntExpr idx = cache.idxStateVar(step);
        IntExpr nextIdx = cache.idxStateVar(step+1);

        BoolExpr wellIncrementedIndex = context.mkEq(nextIdx, context.mkAdd(idx, context.mkInt(1)));

        ArrayExpr<IntSort, BitVecSort> stack_s = cache.stackStateVar(step);
        ArrayExpr<IntSort, BitVecSort> stack_splus1 = cache.stackStateVar(step+1);

        ArrayExpr<IntSort, BitVecSort> expected_stack = context.mkStore(stack_s, idx, (BitVecExpr) this.toBvNum(num));

        BoolExpr expectedEqualsGotten = context.mkEq(stack_splus1, expected_stack);
        
        BoolExpr[] notAlreadyUsed = new BoolExpr[step];
        for (int i = 0; i < step; i++) {
            notAlreadyUsed[i] = cache.pushNumVar(i, num);
        }
        BoolExpr uniquenessConstraint = context.mkNot(context.mkOr(notAlreadyUsed));

        return context.mkImplies(cache.pushNumVar(step, num), context.mkAnd(expectedEqualsGotten, uniquenessConstraint, wellIncrementedIndex));
    }


    private interface ActionVar {
        /**
         * Returns the decision variable for the action at step.
         *
         */
        BoolExpr get(int step);
    }

    private interface ActionResult {
        /**
         * Returns the expression of the action result at step using
         * e1 and e2, the two top values of the stack.
         *
         */
        BitVecExpr get(int step, BitVecExpr e1, BitVecExpr e2);
    }

    private interface ActionPrecondition {
        /**
         * Returns the expression of the action precondition at step
         * using e1 and e2, the two top values of the stack.
         *
         */
        BoolExpr get(int step, BitVecExpr e1, BitVecExpr e2);
    }


    private BoolExpr actionFormula(int step, ActionVar actVar, ActionPrecondition precond, ActionResult opRes) {
        IntExpr indice = cache.idxStateVar(step);
        IntExpr nextIndice = cache.idxStateVar(step+1);

        BoolExpr twoElements = context.mkGe(indice, context.mkInt(2));

        IntExpr i1 = (IntExpr) context.mkSub(indice, context.mkInt(1));
        IntExpr i2 = (IntExpr) context.mkSub(indice, context.mkInt(2));
        
        ArrayExpr<IntSort, BitVecSort> stack = cache.stackStateVar(step);
        ArrayExpr<IntSort, BitVecSort> nextStack = cache.stackStateVar(step+1);
        
        BitVecExpr e1 = (BitVecExpr) context.mkSelect(stack, i1);
        BitVecExpr e2 = (BitVecExpr) context.mkSelect(stack, i2);

        BoolExpr prec = precond.get(step,e1,e2);
        BitVecExpr res = opRes.get(step,e1,e2);
        
        BoolExpr expectedIndice = context.mkEq(i1, nextIndice);
        
        
        ArrayExpr<IntSort, BitVecSort> expected_stack = context.mkStore(stack, i2, res);

        BoolExpr expectedStack = context.mkEq(expected_stack, nextStack);
    
        return context.mkImplies(
            actVar.get(step),
            context.mkAnd(expectedIndice,expectedStack,prec,twoElements)
        );
    }

    /**
     * A boolean formula that should be true iff states at step and
     * step + 1 are linked by a "add" action.
     */
    private BoolExpr addFormula(int step) {
        ActionResult result = (s, e1, e2) -> context.mkBVAdd(e1, e2);
        ActionVar actionVar = cache::addVar;
        ActionPrecondition precondition = (s, e1, e2) -> context.mkTrue();
        return actionFormula(step, actionVar, precondition, result);        
    }

    /**
     * A boolean formula that should be true iff states at step and
     * step + 1 are linked by a "sub" action.
     */
    private BoolExpr subFormula(int step) {
        ActionResult result = (s, e1, e2) -> context.mkBVSub(e1, e2);
        ActionVar actionVar = cache::subVar;
        ActionPrecondition precondition = (s, e1, e2) -> context.mkTrue();
        return actionFormula(step, actionVar, precondition, result);
    }

    /**
     * A boolean formula that should be true iff states at step and
     * step + 1 are linked by a "mul" action.
     */
    private BoolExpr mulFormula(int step) {
        ActionResult result = (s, e1, e2) -> context.mkBVMul(e1, e2);
        ActionVar actionVar = cache::mulVar;
        ActionPrecondition precondition = (s, e1, e2) -> context.mkTrue();
        return actionFormula(step, actionVar, precondition, result);
    }

    /**
     * A boolean formula that should be true iff states at step and
     * step + 1 are linked by a "div" action.
     */
    private BoolExpr divFormula(int step) {
        ActionResult result = (s, e1, e2) -> context.mkBVSDiv(e1, e2);
        ActionVar actionVar = cache::divVar;
        ActionPrecondition precondition = (s, e1, e2) -> context.mkNot(context.mkEq(e2,toBvNum(0)));
        return actionFormula(step, actionVar, precondition, result);
    }

    @Override
    public BoolExpr transitionFormula(int step) {

        BoolExpr[] transitions = new BoolExpr[nums.length+4];
        BoolExpr[] actionTaken = new BoolExpr[nums.length+4];
        for (int i = 0; i < nums.length; i++){
            transitions[i+4] = pushNumFormula(step,nums[i]);
            actionTaken[i+4] = cache.pushNumVar(step, nums[i]);
        }
        transitions[0] = divFormula(step);
        actionTaken[0] = cache.divVar(step);

        transitions[1] = subFormula(step);
        actionTaken[1] = cache.subVar(step);

        transitions[2] = addFormula(step);
        actionTaken[2] = cache.addVar(step);

        transitions[3] = mulFormula(step);
        actionTaken[3] = cache.mulVar(step);

        return context.mkAnd(Z3Utils.exactlyOne(actionTaken),context.mkAnd(transitions));
    }

    @Override
    public void printParams() {
        System.out.println("\nChiffres transition system parameters:");
        System.out.println("- nums       : " + Arrays.toString(nums));
        System.out.println("- target     : " + String.valueOf(target));
        System.out.println("- bvBits     : " + String.valueOf(bvBits));
        System.out.println("- noOverflows: " + String.valueOf(noOverflows));
    }

    /**
     * Prints the stack at step.
     */
    private void printStackAtStep(Model m, int step) {
        int idxState = ((IntNum) m.eval(cache.idxStateVar(step), true)).getInt();

        for (int idx = 0; idx <= maxNofSteps; idx++) {
            BitVecExpr resbv =
                (BitVecExpr) context.mkSelect(cache.stackStateVar(step),
                                              context.mkInt(idx));
            IntExpr resi = context.mkBV2Int(resbv, true);

            if (idx == 0) {
                System.out.print("|");
            }

            if (idx < idxState) {
                System.out.print("|\033[7m");
            } else {
                System.out.print("|");
            }

            System.out.printf("%4d", ((IntNum) m.eval(resi, true)).getInt());

            if (idx < idxState) {
                System.out.print("\033[m");
            }
        }
    }

    @Override
    public void printModel(Model m, int steps) {
        System.out.printf("  init %3s ~> ", " ");
        printStackAtStep(m, 0);
        System.out.println();

        for (int step = 0; step < steps; step++) {
            for (int num : nums) {
                if (m.eval(cache.pushNumVar(step, num), true).isTrue()) {
                    System.out.printf("  push %3d ~> ", num);
                }
            }

            if (m.eval(cache.mulVar(step), true).isTrue()) {
                System.out.printf("  mul %4s ~> ", " ");
            }

            if (m.eval(cache.divVar(step), true).isTrue()) {
                System.out.printf("  div %4s ~> ", " ");
            }

            if (m.eval(cache.addVar(step), true).isTrue()) {
                System.out.printf("  add %4s ~> ", " ");
            }

            if (m.eval(cache.subVar(step), true).isTrue()) {
                System.out.printf("  sub %4s ~> ", " ");
            }

            printStackAtStep(m, step + 1);

            System.out.println();
        }
    }
}
