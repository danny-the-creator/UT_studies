package ss.calculator;

import java.util.ArrayList;
import java.util.List;

public class CalculatorStack implements Calculator{
    private List<Double> stack;
    public CalculatorStack(){
        stack = new ArrayList<>(List.of());
    }
    @Override
    public void push(double value) {
        stack.add(value);
    }

    @Override
    public double pop() throws StackEmptyException {
        if (stack.isEmpty()){
            throw new StackEmptyException("List is empty");
        };
        Double result = stack.get(stack.size() - 1);
        stack.remove(stack.size() - 1);
        return result;
    }

    @Override
    public void add() throws StackEmptyException {
        Double x = pop();
        Double y = pop();
        push(x+y);
    }

    @Override
    public void sub() throws StackEmptyException {
        Double x = pop();
        Double y = pop();
        push(y-x);
    }

    @Override
    public void mult() throws StackEmptyException {
        Double x = pop();
        Double y = pop();
        push(x*y);
    }

    @Override
    public void div() throws DivideByZeroException, StackEmptyException {
        Double x = pop();
        Double y = pop();
        if (x == 0) {
            push(Double.NaN);
            throw new DivideByZeroException("Division by 0");
        }
        push(y/x);
    }
    @Override
    public void dup() throws StackEmptyException{
        Double x = pop();
        push(x);
        push(x);
    }
    @Override
    public void mod() throws StackEmptyException{
        Double x = pop();
        Double y = pop();
        push(x % y);
    }
}
