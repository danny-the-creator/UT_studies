package ss.week2;
import java.util.Scanner;

/**
 * Has
/**
 * The ThreeWayLamp class represents a lamp with three brightness settings: low, medium, and high.
 * It follows a cyclic order: off → low → medium → high → off.
 */
public class ThreeWayLamp {

    /**
     * Enum representing all possible lamp settings: off, low, medium, and high.
     */
    public enum LampSettings { off, low, medium, high }

    /**
     * The current setting of the lamp, initialized to the default value 'off'.
     */
    static LampSettings lamp = LampSettings.off;

    /**
     * Prints the current setting of the lamp to the screen.
     *
     * @return The current lamp setting.
     */
    public LampSettings print() {
        System.out.println(lamp);
        return lamp;
    }

    /**
     * Switches to the next lamp setting, following the order: off → low → medium → high → off.
     */
    public static void next() {
        switch (lamp) {
            case off -> lamp = LampSettings.low;
            case low -> lamp = LampSettings.medium;
            case medium -> lamp = LampSettings.high;
            case high -> lamp = LampSettings.off;
        }
    }

    /**
     * Changes the current lamp setting to the specified setting.
     *
     * @param newS The new setting to be applied (off, low, medium, high).
     */
    public static void change(String newS) {
        switch (newS) {
            case "off" -> lamp = LampSettings.off;
            case "low" -> lamp = LampSettings.low;
            case "medium" -> lamp = LampSettings.medium;
            case "high" -> lamp = LampSettings.high;
            default -> System.out.println("Invalid input! Please choose from: off, low, medium, high.");
        }
    }
}
