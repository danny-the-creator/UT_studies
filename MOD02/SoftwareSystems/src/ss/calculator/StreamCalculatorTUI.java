package ss.calculator;

import java.io.InputStreamReader;
import java.io.OutputStreamWriter;

public class StreamCalculatorTUI {
    public static StreamCalculator streamCalculator = new StreamCalculatorClass();
    public static void main(String[] args) {
        InputStreamReader reader = new InputStreamReader(System.in);
        OutputStreamWriter writer = new OutputStreamWriter(System.out);
        streamCalculator.process(reader, writer);

    }
}
