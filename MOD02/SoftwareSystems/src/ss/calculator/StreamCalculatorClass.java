package ss.calculator;

import java.io.*;
import org.junit.jupiter.api.Test;

public class StreamCalculatorClass extends CalculatorStack implements StreamCalculator{
    private static final String PUSH = "push";
    private static final String POP = "pop";
    private static final String ADD = "add";
    private static final String SUB = "sub";
    private static final String MULT = "mult";
    private static final String DIV = "div";
    private static final String DUP = "dup";
    private static final String MOD = "mod";

    /**
     * Process all commands read from the given input, and write the result(s) to the given output.
     * @param input the Reader to read commands from
     * @param output the Writer to write output to
     */
    @Override
    public void process(Reader input, Writer output){
        PrintWriter writer = new PrintWriter(output);
        try (BufferedReader reader = new BufferedReader(input) ){
            String line;
            while ((line = reader.readLine()) != null){
//                System.out.println(line);
                String[] split = line.split("\\s+");
                String command = split[0];
                String number = null;
                if (split.length > 1) {
                    number = split[1];
                }
                try {
                    switch (command){
                        case PUSH -> push(Double.parseDouble(number));
                        case POP -> {
                            writer.println(pop());
                            writer.flush();
                        }
                        case ADD -> add();
                        case SUB -> sub();
                        case MULT -> mult();
                        case DIV -> div();
                        case DUP -> dup();
                        case MOD -> mod();
                        default -> {
                            writer.println("error: Wrong Command");
                            writer.flush();
                        }
                    }
                }catch (StackEmptyException | DivideByZeroException | RuntimeException e ){
                    writer.println("error: " + e);
                    writer.flush();
                }
            }
        } catch (IOException e){
            e.printStackTrace();
        }
    }
}
