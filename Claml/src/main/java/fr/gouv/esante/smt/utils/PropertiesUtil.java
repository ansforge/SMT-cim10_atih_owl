package fr.gouv.esante.smt.utils;

import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.util.Properties;

public class PropertiesUtil {

  public static String getProperties(final String propertieName) {

    String versionString = null;

    // to load application's properties, we use this class
    final Properties mainProperties = new Properties();

    FileInputStream file;

    // the base folder is ./, the root of the main.properties file
    final String path = "./claml.properties";

    // load the file handle for main.properties
    try {
      file = new FileInputStream(path);
      // load all the properties from this file
      mainProperties.load(file);
      // retrieve the property we are intrested, the app.version
      versionString = mainProperties.getProperty(propertieName);
      // we have loaded the properties, so close the file handle
      file.close();
    } catch (final FileNotFoundException e) {
      // TODO Auto-generated catch block
      e.printStackTrace();
    } catch (final IOException e) {
      // TODO Auto-generated catch block
      e.printStackTrace();
    }



    return versionString;
  }
  
  public static String getPlagesReference(final String propertieName) {

	    String versionString = null;

	    // to load application's properties, we use this class
	    final Properties mainProperties = new Properties();

	    FileInputStream file;

	    // the base folder is ./, the root of the main.properties file
	    final String path = "./listPlagesReference.txt";

	    // load the file handle for main.properties
	    try {
	      file = new FileInputStream(path);
	      // load all the properties from this file
	      mainProperties.load(file);
	      // retrieve the property we are intrested, the app.version
	      versionString = mainProperties.getProperty(propertieName);
	      // we have loaded the properties, so close the file handle
	      file.close();
	    } catch (final FileNotFoundException e) {
	      // TODO Auto-generated catch block
	      e.printStackTrace();
	    } catch (final IOException e) {
	      // TODO Auto-generated catch block
	      e.printStackTrace();
	    }



	    return versionString;
	  }

}
