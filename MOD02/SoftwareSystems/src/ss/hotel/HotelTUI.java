package ss.hotel;

import java.util.Scanner;
import ss.hotel.bill.Bill;
import ss.hotel.password.Password;

public class HotelTUI {
    private Hotel hotel;

    public HotelTUI(Hotel hotel) {
        this.hotel = hotel;
    }

    static private final String IN = "in";
    static private final String OUT = "out";
    static private final String ROOM = "room";
    static private final String ACTIVATE = "activate";
    static private final String HELP = "help";
    static private final String PRINT = "print";
    static private final String EXIT = "exit";

    private void menu() {
        System.out.println("Welcome to the Hotel management system of the \"Hotel Twente\"");
        System.out.println("in name ................. check in guest with name");
        System.out.println("out name ................ check out guest with name");
        System.out.println("room name ............... request room of guest with name");
        System.out.println("activate name ........... activate safe of guest with name");
        System.out.println("help .................... help (this menu)");
        System.out.println("print ................... print state");
        System.out.println("exit .................... exit");
    }

    private void run() {
        menu();
        Scanner scanner = new Scanner(System.in);
        while (true) {
            System.out.println("What do you want to do?");
            String input = scanner.nextLine();
            String[] split = input.split("\\s+");
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
                    // activate safe of guest with name
                    doActivate(name);
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

    private void doOut(String name) {
        if (name == null) {
            System.out.println("Name shouldn't be null.");
        } else {
            if (hotel.getRoom(name) == null) {
                System.out.println(name + " was not checked in.");
            } else {
                System.out.printf(name + " is check out of room %d.\n",
                                  hotel.getRoom(name).getNumber());
                hotel.getRoom(name).getGuest().checkout();
            }
        }
    }

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

    public static void main(String[] args) {
        Hotel hotel = new Hotel("Hotel Twente");
        HotelTUI tui = new HotelTUI(hotel);
        tui.run();
    }
}