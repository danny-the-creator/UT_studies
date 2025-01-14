package ss.hotel;

import java.util.Scanner;
import ss.hotel.bill.Bill;
import ss.hotel.bill.StringBillPrinter;


public class PricedHotelTUI {
    private PricedHotel hotel;


    public PricedHotelTUI(PricedHotel hotel) {
        this.hotel = hotel;
    }

    static private final String IN = "in";
    static private final String OUT = "out";
    static private final String ROOM = "room";
    static private final String ACTIVATE = "activate";
    static private final String BILL = "bill";
    static private final String HELP = "help";
    static private final String PRINT = "print";
    static private final String EXIT = "exit";

    public String[] split;

    /**
     * Displays the main menu with available commands for the PricedHotelTUI.
     */
    private void menu() {
        System.out.println("Welcome to the Hotel management system of the \"Hotel Twente\"");
        System.out.println("in name ................. check in guest with name");
        System.out.println("out name ................ check out guest with name");
        System.out.println("room name ............... request room of guest with name");
        System.out.println("activate name password .. activate safe, password required for PricedSafe");
        System.out.println("bill name nights......... print bill for guest (name) and number of nights");
        System.out.println("help .................... help (this menu)");
        System.out.println("print ................... print state");
        System.out.println("exit .................... exit");
    }

    /**
     * execute commands in a loop
     */
    private void run() {
        menu();
        Scanner scanner = new Scanner(System.in);
        while (true) {
            System.out.println("What do you want to do?");
            String input = scanner.nextLine();
            split = input.split("\\s+");
            // Split the input line on one or more whitespace characters.
            String command = split[0];
            String name = null;
            if (split.length > 1) {
                name = split[1];
            }
            switch (command) {
                case EXIT:
                    return;
                case IN:
                    doIn(name);
                    continue;
                case OUT:
                    doOut(name);
                    continue;
                case ROOM:
                    doRoom(name);
                    continue;
                case ACTIVATE:
                    if (hotel.getRoom(name) instanceof PricedRoom){
                        if (split.length <3){ System.out.println("The password should be provided!");} else {
                            doActivatePriced(name, split[2]);
                        }

                    }else {
                        // activate safe of guest with name
                        doActivate(name);
                    }
                    continue;
                case BILL:
                    getBill(name, Integer.parseInt(split[2]));
                    continue;
                case HELP:
                    // activate safe of guest with name
                    menu();
                    continue;
                case PRINT:
                    System.out.println(hotel.toString());
                    continue;
                default:
                    System.out.println("Wrong format of input.");
                    menu();
            }
        }

    }

    /**
     * Handle check-in operation
     * @param name Name of the client
     */
    //@requires name!=null;
    //@ensures hotel.getRoom(name) != null ==> hotel.getRoom(name).getGuest() != null;
    private void doIn(String name) {
        if (name == null) {
            System.out.println("Name shouldn't be null.");
        } else {
            Room room = this.hotel.checkIn(name);
            if (room == null) {
                System.out.println(name + " check in unsuccessful.");
            } else {
                System.out.println(name + " gets " + room.toString());
            }
        }
    }

    /**
     * Handle check-out aperation
     * @param name of the guest
     */
    //@ requires name!= null;
    //@ ensures !hotel.getRoom(name).getSafe().isActive() && hotel.getRoom(name) == null ;
    private void doOut(String name) {
        if (name == null) {
            System.out.println("Name shouldn't be null.");
        } else {
            if (hotel.getRoom(name) == null) {
                System.out.println(name + " was not checked in.");
            } else {
                System.out.printf(name + " is check out of room %d.\n",
                                  hotel.getRoom(name).getNumber());
                hotel.getRoom(name).getSafe().deactivate();
                hotel.getRoom(name).getGuest().checkout();
            }
        }
    }

    /**
     * Returns the room of the guest with this name
     * @param name of the guest
     */
    //@requires name!= null;
    //@ ensures hotel.getRoom(name) == null || hotel.getRoom(name).toString() != null;
    private void doRoom(String name) {
        if (name == null) {
            System.out.println("Name shouldn't be null.");
        } else {
            Room room = hotel.getRoom(name);
            if (room == null) {
                System.out.println(name + "  doesn't have a room.");
            } else {
                System.out.println(name + " has " + room.toString());
            }
        }
    }

    /**
     * Activates the safe of the guest with a givven name
     * @param name of the guest
     */

    //@ requires name!= null;
    //@ ensures hotel.getRoom(name) != null ==> hotel.getRoom(name).getSafe().isActive();
    private void doActivate(String name) {
        if (name == null) {
            System.out.println("Name shouldn't be null.");
        } else {
            Room room = hotel.getRoom(name);
            if (room == null) {
                System.out.println("Don't have a room for " + name);
            } else {
                room.getSafe().activate();
                System.out.println("Safe of guest " + name + " is activated");
            }
        }
    }

    /**
     * Activates the safe of the guest with a given name if he entered the right password
     * @param name of the guest
     * @param password to open the safe
     */
    //@ requires name!= null && password!=null;
    //@ ensures hotel.getRoom(name) != null && password == "default" ==> hotel.getRoom(name).getSafe().isActive();;
    private void doActivatePriced(String name, String password){
        PricedRoom room = (PricedRoom) hotel.getRoom(name);
        if (room == null){
            System.out.println("Don't have a room for " + name);
        } else{
            ((PricedSafe) room.getSafe()).activate(password);
            if (room.getSafe().isActive()){
                System.out.println("Safe of guest " + name + " is activated");
            } else {
                System.out.println("Wrong Password!");
            }
        }
    }

    /**
     * Prints the bill for the guest with a given name (including prices for rooom and for the safe)
     * @param name of the guest
     * @param nNights   number of nights the guest spent in the hotel
     */
    //@requires name != null && nNights >= 0;
    private void getBill(String name, int nNights){
        StringBillPrinter stringBillPrinter = new StringBillPrinter();
        Bill bill = hotel.getBill(name, nNights,stringBillPrinter );
        System.out.println(stringBillPrinter.getResult());
    }

    public static void main(String[] args) {
        PricedHotel hotel = new PricedHotel("Hotel Twente");
        PricedHotelTUI tui = new PricedHotelTUI(hotel);
        tui.run();
    }
}